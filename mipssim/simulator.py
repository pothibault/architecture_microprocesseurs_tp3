# -*- coding: utf-8 -*-
#
# Copyright (c) 2011-2014, Julien-Charles Lévesque <levesque.jc@gmail.com>
#  and contributors.
#
# Distributed under the terms of the MIT license. See the COPYING file at
#  the top-level directory of this project and at
#  https://bitbucket.org/ulaval-gif-3000/mipssim/raw/tip/COPYING

import sys

from collections import OrderedDict, deque
from xml.dom.minidom import parse

#local imports
import trace
import interpreter as interp
from interpreter import memory_re
import components
from components import State


class Simulator:
    '''
    Simulateur d'exécution du MIPS.

    Prends le code retourné par l'interpreteur et l'exécute sur la
    configuration entrée.
    '''
    def __init__(self, config_file, source_file, trace_file='', latex_trace_file='', debug=False):
        #Initialisation des variables membres
        self.clock = 1
        self.stall = False
        self.new_PC = None
        self.ROB = components.ROB(maxlen=24)
        self.PC = -1 #Puisqu'on incrémente avant le premier lancement
        self.RS = OrderedDict()
        self.lancements = 1
        self.sanctions = 1

        self.debug = debug

        #Initialisation des registres
        self.regs = components.Registers()

        #Lecture de la configuration et du code source à exécuter
        self.load_config(config_file)
        self.instructions = interp.interpret_asm(source_file)

        #Setup du fichier de trace si applicable
        self.trace = []
        if trace_file:
            self.trace.append(trace.TextTrace(trace_file))
        if latex_trace_file:
            self.trace.append(trace.LaTeXTrace(latex_trace_file))

    def go(self):
        '''
        Effectue la simulation

        Valeurs de retour:

        * 0 = Simulation terminée avec succès
        * 1 = Une erreur a été détectée lors de l'exécution du programme. Pour
              plus de détails, voir le flot d'erreur du programme.
        * 2 = Une erreur non-prévue s'est produite.
        '''

        while self.step() == 0:
            self.clock += 1

        #L'exécution s'est complétée sans problème.
        print("Simulation terminée au coup d'horloge %i." % self.clock)
        return 0

    def step(self):
        '''
        Effectue une itération de la simulation.

        * Retourne 0 si l'opération s'est déroulée avec succès et l'exécution
        n'est pas terminée.
        * Retourne 1 si l'opération s'est déroulée avec succès et l'exécution
        est terminée
        '''
        #Les opérations sont inversées pour éviter d'accomplir plusieurs actions sur une même
        # instruction dans un seul coup d'horloge.

        #On sanctionne l'instruction via le ROB ( Premier élément de celui-ci )
        committed = 0
        while committed < self.sanctions:
            if not self.commit():
                break
            committed += 1

        #Décrémentation du temps sur les unités fonctionnelles
        self.decrement_time()

        issued = 0

        while issued < self.lancements:
            # Gestion des bulles et de la fin du programme
            if self.stall == True or (self.new_PC == None and self.PC + 1 == len(self.instructions)):
                break
            elif self.new_PC == len(self.instructions):
                #Le programme va terminer son exécution dès que le ROB sera vide.
                self.PC = self.new_PC
                break
            else:
                #Avancement du Issue/Program Counter (PC)
                if self.new_PC != None: #Si branchement
                    self.PC = self.new_PC
                else:
                    self.PC = self.PC + 1
                self.new_PC = None

                old_PC = self.PC
                self.issue()
                issued += 1

        if issued == 0:
            print('Aucune instruction lancée (clock: %i).' % self.clock)

        #Mise à jour de la trace
        for t in self.trace:
            t.update(self)

        #Si l'exécution est terminée et le ROB est vide
        if self.PC + 1 >= len(self.instructions) and len(self.ROB) == 0:
            return 1
        else:
            return 0

    def commit(self):
        '''
        Sanctionne les opérations dont le calcul est terminé dans l'ordre de lancement.
        Seule l'instruction à la tête du ROB peut être sanctionnée.
        '''
        if len(self.ROB) == 0:
            return False

        rob_head = self.ROB[self.ROB.start]

        #Petit hack pour pouvoir visualiser la dernière entrée à avoir été sanctionnée
        if rob_head.state == State.COMMIT:
            self.ROB.free_head_entry()
            if len(self.ROB) == 0:
                return False
            rob_head = self.ROB[self.ROB.start]

        if len(self.ROB) > 0 and rob_head.state == State.WRITE and rob_head.ready:
            if self.debug:
                print('Sanctionnement: %s' % rob_head)

            if rob_head.dest != None:
                self.regs[rob_head.dest] = rob_head.value
                #Si cette instruction était la seule (ou la dernière) à devoir écrire dans le ROB,
                #effacer le marqueur à cet effet dans regs.stat
                if self.regs.stat[rob_head.dest] != None:
                     dest_i = self.regs.stat[rob_head.dest]
                     if dest_i == rob_head.i:
                         self.regs.stat[rob_head.dest] = None

            # Gestion des branchs lors du sanctionnement
            if rob_head.instr.funit_type == 'Branch':
                self.stall = False
                if (rob_head.prediction != rob_head.value):
                    # Mauvaise spéculation
                    #Si il y avait un blocage, il disparaît car on flush le ROB et les RS
                    if rob_head.value:
                        #On force la prise de ce branchement
                        self.new_PC = int(rob_head.instr.operands[-1][1:])
                    else:
                        #On retourne à l'instruction suivant le branchement
                        self.new_PC = rob_head.instr.addr + 1

                    #Flush le ROB
                    self.ROB.reset()

                    #Remet les drapeaux d'écriture des registres à None
                    self.regs.reset_stat()

                    #Clean les stations de réservation
                    self.reset_funits()
                    return
                else:
                    # Spéculation réussite, aucun changement requis.
                    pass
            elif rob_head.instr.funit_type == 'Store':
                #On écrit le résultat en mémoire.
                self.mem[rob_head.addr] = rob_head.value

            # Une fois l'instruction sanctionnée, on la conserve pendant un coup d'horloge
            rob_head.state = State.COMMIT
            return True
        
        return False

    def exec_instr(self, func_unit, rob_entry):
        '''
        Termine l'exécution de l'instruction dans ´func_unit´. Place les résultats aux bons
         endroits.

        Paramètres:
        -----------

        func_unit: Unité fonctionnelle dans laquelle l'instruction à compléter se trouve.
        rob_entry: Entrée correspondante dans le ROB.
        '''
        instr = rob_entry.instr

        if func_unit.name[:-1] == 'Branch':
            #Déterminer si le branchement est pris.
            branch = False
            if instr.code == 'BEQ':
                if func_unit.vj == func_unit.vk:
                    branch = True
            elif instr.code == 'BNE':
                if func_unit.vj != func_unit.vk:
                    branch = True
            elif instr.code == 'BEQZ':
                if func_unit.vk == 0:
                    branch = True
            elif instr.code == 'BNEZ':
                if func_unit.vj != 0:
                    branch = True
            elif instr.code == 'J':
                branch = True
            else:
                raise Exception('Instruction de branchement inconnue (%s).' % (instr.code))
            #On place le comportement final du branchement dans le ROB.
            rob_entry.value = branch

            #On communique le résultat du branchement à l'unité de branchement pour
            #mettre à jour son modèle (si applicable)
            func_unit.update(branch)
        elif func_unit.name[:-1] == 'Store':
            #On a calculé la destination du Store au début de son exécution, reste donc rien à faire
            #pour cette étape.
            pass
        elif func_unit.name[:-1] == 'Load':
            #Le load ne pouvait pas s'exécuter tant qu'un store le précédait dans le ROB,
            #rendu ici, on est certain qu'il n'y aura pas de problème.
            if instr.code == 'LD':
                load_type = 'int'
            elif instr.code == 'L.D':
                load_type = 'float'
            else:
                raise Exception('Instruction Load inconnue (%s).' % (instr.code))
            rob_entry.value = self.mem.load(func_unit.A, load_type)
        else:
            result = eval('%s %s %s' % (func_unit.vj, instr.operator, func_unit.vk))
            rob_entry.value = result

        rob_entry.state = State.EXECUTE

    def resolve_operand(self, operand):
        '''
        Résout une variables en code MIPS, celle-ci peut être convertie directement (immediate),
         ou lue dans le registre correspondant (FXX/RXX). Si le registre est occupé, on retourne
         un pointeur vers l'entrée du ROB qui produira cette valeur.
        '''
        #Cas le plus simple, valeur immédiate
        if operand[0] == '#':
            value = int(operand[1:])
            rob_i = None
        #Registre
        elif operand[0] in ['R', 'F']:
            #On vérifie si le registre attend après une autre instruction (on évite les WAR)
            rob_i = self.regs.stat[operand]
            value = self.regs[operand]
            #Registre en attente, on met seulement un pointeur vers l'entrée ROB
            if rob_i != None:
                rob_i = rob_i
                value = None
        else:
            raise Exception('Opérande invalide.')
        return value, rob_i

    def resolve_memory_operand(self, operand):
        '''Résout une opérande concernant un accès mémoire.'''
        reg_name = operand.split('(')[1].split(')')[0]
        mem_adr_value, rob_i = self.resolve_operand(reg_name)

        #décalage immédiat de l'adresse: IMM(RX)
        mem_imm = int(operand.split('(')[0])

        return mem_imm, mem_adr_value, rob_i

    def reset_funits(self):
        '''Remet toutes les unités fonctionnelles à leur état initial.'''
        for _, funit_type in self.RS.items():
            # Prendre une référence sur l'unité fonctionnelle qu'on analyse
            for funit in funit_type:
                funit.reset()

    def decrement_time(self):
        '''
        Effectue un coup d'horloge, soit décrémente de un le temps restant de chaque unité
         fonctionnelle qui travaille en ce moment.

        Démarre les unités fonctionelles qui attendaient des données maintenant disponibles.
        '''
        #Variable temporaire pour savoir si nous avons mis à jour une UF.
        updated = [[False] * len(funit) for _, funit in self.RS.items()]

        #Première passe, les instructions devant fournir des opérandes doivent le faire
        #avant de tenter d'exécuter quoi que ce soit.
        #Les unités fonctionnelles sont regroupées par type dans la structure RS pour ReservationStations
        #Par exemple {'Load':[Load1, Load2], 'Store':[Store1, Store2], ...}
        for i, (unit_type, units) in enumerate(self.RS.items()):
            #Itérer sur les unités fonctionnelles dans la station de réservation
            for j, funit in enumerate(units):
                # Vérifier que l'unité est actuellement utilisée :
                if funit.busy:
                    # Si elle est déjà partie...
                    if funit.time != None:
                        updated[i][j] = True
                        #Si on passe de 0 à -1, l'unité redevient disponible et le résultat est
                        # écrit (Write de Tomasulo)
                        if funit.time < 1:
                            #Calcule le résultat
                            exec_rob_entry = self.ROB[funit.dest]
                            self.exec_instr(funit, exec_rob_entry)

                            # Writeback Tomasulo, écriture de l'instruction sur le CDB et mise à
                            # jour des stations de réservation
                            success = self.writeback_tomasulo(funit, funit.dest, exec_rob_entry.value)
                            if success:
                                funit.reset()
                            #Le writeback peut échouer dans le cas d'un Store... on va réessayer au
                            #prochain coup d'horloge.

                        # Sinon, simplement la décrémenter de 1
                        else:
                            funit.time -= 1
                            #L'unité est en train de s'exécuter, donc on l'indique.
                            self.ROB[funit.dest].state = State.EXECUTE

        #Seconde passe, tenter de démarrer l'exécution des unités fonctionnelles en attente d'opérandes.
        for i, (unit_type, units) in enumerate(self.RS.items()):
            for j, funit in enumerate(units):
                # Vérifier que l'unité est actuellement utilisée et qu'elle n'a pas été mise à jour dans
                # la passe précédente :
                if funit.busy and not updated[i][j]:
                    # Si l'unité fonctionnelle n'est pas démarrée (temps = None), vérifier si on peut la partir
                    self.start_exec(funit, self.ROB[funit.dest])

    def issue(self):
        '''
        Ajouter une instruction dans le ROB pendant son calcul par une unité fonctionelle.
        '''
        #Référence vers le conteneur pour toutes les unités fonctionnelles du type courant
        cur_instruction = self.instructions[self.PC]
        func_unit_ref = self.RS[cur_instruction.funit_type]
        #Vérifie si une unité fonctionnelle du type requis est libre
        funit_idx = self.find_funit(func_unit_ref, cur_instruction.funit_type)

        # Attribuer l'opération à une station de réservation si possible
        if funit_idx > -1 and self.ROB.check_free_entry():
            cur_funit = func_unit_ref[funit_idx]
            cur_funit.reset()

            if self.debug:
                print('Lance l\'instruction :', cur_instruction)

            #Occuper une place dans le ROB
            cur_rob_i, cur_rob_entry = self.ROB.get_free_entry()
            cur_rob_entry.instr = cur_instruction
            cur_rob_entry.state = State.ISSUE
            cur_rob_entry.ready = False
            cur_rob_entry.funit = cur_funit.name

            #Occuper l'unité fonctionnelle
            cur_funit.occupy(cur_instruction)

            # Vérifier les paramètres des opérations voir s'ils vont dans le vj/vk ou qj/qk
            if cur_instruction.funit_type == 'Store':
                to_check = [0, 1]
            elif cur_instruction.funit_type == 'Branch':
                if cur_instruction.code in ['BEQZ', 'BNEZ']:
                    to_check = [0]
                elif cur_instruction.code in ['BEQ', 'BNE']:
                    to_check = [0, 1]
                else:
                    to_check = []
            else:
                to_check = [1, 2]

            # Trouver Vj/Vk ou Qj/Qk
            first_operand = True
            for i in to_check:
                if len(cur_instruction.operands) < i + 1:
                    continue
                raw_operand = cur_instruction.operands[i]
                if self.debug:
                    print('Traite l\'opérande ', raw_operand)

                # Est-ce qu'on a déjà la valeur? Si oui, on la met dans Vj/Vk, sinon, Qj/Qk
                # Ne pas résoudre les accès mémoire en ce moment
                memory_operand = memory_re.match(raw_operand) is not None
                if memory_operand:
                    mem_imm, value, rob_i = self.resolve_memory_operand(raw_operand)
                    cur_funit.A = mem_imm
                else:
                    value, rob_i = self.resolve_operand(raw_operand)

                #Si nous n'avons pas encore la valeur de cette opérande
                if rob_i is not None:
                    waiting_op_rob = self.ROB[rob_i]
                    #Si cette instruction avait terminé de s'exécuter, on peut
                    #prendre son résultat
                    if waiting_op_rob.state == State.WRITE or waiting_op_rob.state == State.COMMIT:
                        value = waiting_op_rob.value
                        value_ready = True
                    #Sinon on place un pointeur vers le ROB.
                    else:
                        value = rob_i
                        value_ready = False
                #Sinon value contiendra une donnée valide et prête à utiliser.
                else:
                    value_ready = True

                if first_operand:
                    if value_ready:
                        cur_funit.vj = value
                    else:
                        #Utiliser la valeur de format '#ROB' plutôt
                        #que le numéro de registre directement
                        cur_funit.qj = value
                else:
                    if value_ready:
                        cur_funit.vk = value
                    else:
                        #Utiliser la valeur de format '#ROB' plutôt
                        #que le numéro de registre directement
                        cur_funit.qk = value
                first_operand = False

            #Tente de démarrer l'exécution (elle ne débutera réellement qu'au prochain appel
            # à decrement_time)
            self.start_exec(cur_funit, cur_rob_entry)

            # Trouver le paramètre de destination, qui est l'inverse des paramètres d'entrée (sauf pour le Branch)
            destination = [a for a in range(len(self.instructions[self.PC].operands)) if a not in to_check]
            # Si l'opération est un branch, aucune destination à analyser - c'est un label.
            # Si aucune destination trouvée, i.e. un Store ou  Branch, mettre à None
            if len(destination) > 0 and self.instructions[self.PC].funit_type != 'Branch':
                destination = destination[0]
            else:
                destination = None

            # Mettre une référence dans la destination, soit #ROB
            if destination is not None:
                cur_rob_entry.dest = self.instructions[self.PC].operands[destination]
                #Indiquer que le registre attend une valeur de `cur_rob_i`
                self.regs.stat[self.instructions[self.PC].operands[destination]] = cur_rob_i

            #La destination pour l'UF est toujours l'entrée ROB correspondante.
            cur_funit.dest = cur_rob_i

            if self.debug:
                print('Debug: cur_rob_entry: ', cur_rob_entry)
                print('Debug: cur_funit: ', cur_funit)

            # Gestion des branchs / Spéculation
            if self.instructions[self.PC].funit_type == 'Branch':
                # adresse du branchement
                cur_funit.A = int(self.instructions[self.PC].operands[-1][1:])

                # Demande la prédiction à notre unité de branchement (celle-ci doit définir
                # la fonction get_prediction(pc, dest)
                #Hennessy ne spécifie pas où placer la prédiction
                cur_rob_entry.prediction = cur_funit.get_prediction(self.PC, cur_funit.A)

                #Prédiction d'un branchement pris.
                if cur_rob_entry.prediction == True:
                    self.new_PC = cur_funit.A
                #Sinon aucune action à prendre.
        else:
            # Aucune unité fonctionnelle libre trouvée ou bien plus de place dans le ROB
            # On est coincés comme des rats, on attend.
            self.new_PC = self.PC

    def start_exec(self, funit, rob_e):
        '''
        Démarre l'exécution d'une instruction. Retournera True si l'instruction s'est bien
         démarrée, ou False sinon.
        '''
        instr = funit.instr

        #On vérifie les conditions pour le démarrage de l'exécution
        ready = False
        if instr.funit_type == 'Store':
            #Le Store n'a besoin que du Qk pour démarrer son exécution
            if funit.qk == None:
                ready = True
                #Calcule automatiquement l'addresse.
                if funit.vk != None:
                    funit.A = funit.vk + funit.A
                    rob_e.addr = funit.A
                    funit.vk = None
        elif instr.funit_type == 'Load':
            #On calcule la première étape du Load immédiatement
            if funit.qj == None:
                #N'exécuter ce bloc qu'une seule fois.
                if funit.vj != None:
                    funit.A = funit.vj + funit.A
                    funit.vj = None
            else:
                #Pas prêt pour l'exécution
                return False

            wait_for_store = False
            for e in self.ROB:
                #Arrivé à l'instruction courante, cesse de parcourir le ROB
                if e.i == funit.dest:
                    break
                if e.instr.funit_type == 'Store':
                    #Convention différente pour stocker l'addresse de destination, car le Store
                    #lit l'addresse mémoire après que l'unité fonctionnelle ait été relâchée.
                    #Si on ne sait pas où va écrire le Store ou s'il va écrire à la même adr
                    if e.addr == None or e.addr == funit.A:
                        wait_for_store = True
                        break
            if not wait_for_store:
                ready = True
        else:
            if funit.qj == None and funit.qk == None:
                ready = True

        #Démarre l'exécution si les conditions sont rencontrées.
        if ready:
            if instr.funit_type == 'Mult':
                #Temps d'exécution différents pour multiplication et division
                if instr.action.find('*') > -1:
                    funit.time = funit.latency
                else:
                    funit.time = funit.div_latency
            else:
                funit.time = funit.latency
            return True
        return False

    def writeback_tomasulo(self, wb_funit, wb_rob_entry_idx, value=None):
        '''
        Une fois l'exécution d'une instruction terminée, il est possible de placer sa valeur
         sur le CDB et donc de mettre à jour les unités fonctionnelles attendant cette valeur.
        '''
        rob_entry = self.ROB[wb_rob_entry_idx]
        #Le Store procède différemment
        if wb_funit.instr.funit_type == 'Store':
            if wb_funit.qj == None: #Différent de la convention d'Hennessy... pas dramatique.
                rob_entry.value = wb_funit.vj
            else:
                #Store pas prêt pour Writeback.
                return False
        else:
            for _, funit_type in self.RS.items():
                for funit in funit_type:
                    #Mise à jour requise uniquement lorsque l'unité attend ses paramètres.
                    if funit.qj == wb_rob_entry_idx:
                        funit.vj = value
                        funit.qj = None
                    if funit.qk == wb_rob_entry_idx:
                        funit.vk = value
                        funit.qk = None
            rob_entry.value = value

        #Writeback complété
        rob_entry.ready = True
        rob_entry.state = State.WRITE
        #Libère l'unité fonctionnelle
        wb_funit.reset()
        return True

    def find_funit(self, funits, name):
        '''
        Prend une liste d'unités fonctionnelles en entrée, cherche une unité qui est n'est pas
        occupée (variable busy à False).
        '''
        for i, funit in enumerate(funits):
            if funit.busy:
                continue
            #TODO JCL: S'assurer que l'unité fonctionnelle n'est plus impliquée dans le ROB
            return i
        return -1

    def load_config(self, config_file):
        '''
        Initialise le simulateur en fonction de ce qui est défini dans le fichier XML
         de configuration.
        '''

        # Ouvrir le fichier XML
        try:
            print('Lecture du fichier de configuration %s en cours...' % config_file)
            xml_data = parse(config_file)
            print('Fichier de configuration lu avec succès.')
        except:
            raise Exception('Impossible d\'utiliser le fichier de configuration '
                'XML.')

        self.RS['Load'] = create_functional_units(xml_data, 'Load', 1, 1)
        self.RS['Store'] = create_functional_units(xml_data, 'Store', 1, 1)
        self.RS['Add'] = create_functional_units(xml_data, 'Add', 1, 1)
        self.RS['Mult'] = create_functional_units(xml_data, 'Mult', 1, 1,
         additional_defaults={'div_latency': 1})
        self.RS['ALU'] = create_functional_units(xml_data, 'ALU', 1, 1)
        self.RS['Branch'] = create_functional_units(xml_data, 'Branch', 1, 1)

        #Lancements et sanctions
        root = xml_data.getElementsByTagName('MIPSSim')[0]

        lancements = root.getAttribute('lancements')
        sanctions = root.getAttribute('sanctions')

        self.lancements = int(lancements) if lancements else 1
        self.sanctions = int(sanctions) if sanctions else 1

        # Attribution des registres
        register_nodes = xml_data.getElementsByTagName('Registers')[0].childNodes
        register_nodes = zip(register_nodes[::2], register_nodes[1::2])
        for a in register_nodes:
            name = a[1].tagName
            value = a[1]._attrs['value'].value
            self.regs[name] = value

        # Attribution de la mémoire
        try:
            mem_init_values = xml_data.getElementsByTagName('Memory')[0].childNodes[0].data.strip().split()
        except:
            mem_init_values = []
        mem_size = int(xml_data.getElementsByTagName('Memory')[0]._attrs['size'].value)
        self.mem = components.Memory(mem_size, mem_init_values)

def update_operands(funit, rob_entry):
    '''
    Remplace les opérandes dans qk et/ou qj avec les valeurs nouvellement calculées.
    '''
    if funit.qj == rob_entry.i:
        funit.vj = rob_entry.value
        funit.qj = None
    if funit.qk == rob_entry.i:
        funit.vk = rob_entry.value
        funit.qk = None


def create_functional_units(xml_data, name, default_n, default_latency, additional_defaults={}):
    '''
    Créé une liste d'unités fonctionnelles de type `name` et tente de charger une configuration
    pour ce type dans `xml_data`.
    '''

    fu_params = {}
    fu_params.update(additional_defaults)
    #Les paramètres par défaut vont être écrasés.
    fu_params['number'] = default_n
    fu_params['latency'] = default_latency

    try:
        elements = xml_data.getElementsByTagName(name)[0]
        for k, v in elements._attrs.items():
            fu_params[k] = v.value
    except IndexError as id:
        print('Aucune configuration trouvée pour les unités fonctionnelles de type %s.'
            % name)

    #Possibilité de mettre un champ 'class' dans le fichier de configuration XML
    #On tentera alors d'aller chercher une classe avec ce nom dans le fichier components.py
    if 'class' in fu_params:
        cl = fu_params.pop('class')
    elif name == 'Branch':
        cl = 'BranchUnit'
    else:
        cl = 'FuncUnit'

    #Générer les unités fonctionnelles
    n = int(fu_params.pop('number'))
    funit_cl = components.__getattribute__(cl)
    funits = [funit_cl(name='%s%i'%(name, i+1), **fu_params) for i in range(n)]

    return funits


if __name__ == '__main__':
    sys.stderr.write('Ce module n\'est pas utilisable seul.')
    sys.exit(-1)
