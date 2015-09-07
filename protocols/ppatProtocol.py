# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

"""
This module provide 4 classes:
    - Circuit
    - Gate
    - Worker
    - Client
Communications between Worker and Clients are simulated through function calls.
Each Client and the Worker receive the same copy of the circuit that is used to
compute or verify the function.
- Circuit is a collection of gates with input gates, outputgates and gates (including i/o gates)
- Gate contains pointers to its inputs gates, it also refers to an operation and
stores a value that is the result of the operation on the inputs gates.

Note that the Worker has access to a secret key (e.g. of the ppats scheme) and the
clients have access to the public key.

Each circuit and gates runs on multiple levels, that is for example, a level on
commitments, a level of message and a level of ciphertext. Therefore, each operation
in the gates have to be defined on these different levels. For example, an addition
over two message translates in a multiplication over commitments. In this case, the
label of the operation is addition, but the operation is specifically definde for the
different levels.

Moreover, some operations require a proof of knowledge to be executed. In this case,
the result is stored as well as the proof. Comparable to what was done for the operands,
a dictionnary must store the functions to be called to perform the proof and to check them.

Worker and Client classes can be used as abstract classes for the worker and the
clients of specific applications
"""
import nizkproofs.nizkpok as nizk

class Circuit:
    def __init__(self,inputs=None,outputs=None,gates=None,label=None,operandsdict={},neutralsdict={}):
        self.inputs = inputs # collection of input gates
        self.outputs = outputs # collection of output gates
        self.gates = gates # collection of gates
        self.label = label
        self.operandsdict = operandsdict
        self.neutralsdict = neutralsdict
        for key in self.operandsdict :
            assert key in self.neutralsdict
        assert len(self.operandsdict) == len(self.neutralsdict)

    def __str__(self):
        if self.gates == None :
            return "empty circuit"
        else :
            s = "Circuit "+str(self.label)+" containing "+str(len(self.gates))+" gates with :\n INPUT GATES\n"
            for g in self.inputs:
                s = s+str(g)+"\n"
            s = s+"\n OTHER GATES \n"
            for g in self.gates:
                if not g in self.inputs and not g in self.outputs :
                   s = s+str(g)+"\n"
            s = s+"\n OUTPUT GATES \n"
            for g in self.outputs:
                s = s+str(g)+"\n"
            return s

    def compute(self,levels=None,gates=None,recompute=False, multipass = True, taggatedict = {}):
        if multipass == False and taggatedict == {}:
            for gate in self.gates :
                taggatedict[repr(gate)] = 'not visited'
        if gates == None :
            gates = self.outputs
        if levels == None :
            levels = gates[0].valuedict.keys()
        for l in levels :
            for gate in gates :
                if multipass == False and taggatedict[repr(gate)] == 'visited' :
                    pass
                elif not gate.inputs == None :
                    for inputgate in gate.inputs :
                        #print inputgate
                        if inputgate.valuedict[l] == None or recompute :
                            self.compute([l],[inputgate],recompute,multipass,taggatedict)
                        else:
                            pass
                    gate.compute([l])
                    if multipass == False :
                        taggatedict[repr(gate)] = 'visited'

    def addLevels(self,levels,newoperandsdict = {},newneutralsdict = {}):
        for l in levels :
            if (l in newoperandsdict) and (l in newneutralsdict) :
                for gate in self.gates :
                    gate.operanddict.setdefault(l)
                    if not gate.operandname == None :
                        gate.operanddict[l] = newoperandsdict[l][gate.operandname]
                    gate.proofdict.setdefault(l)
                    gate.valuedict.setdefault(l)
                self.operandsdict.setdefault(l)
                self.operandsdict[l] = newoperandsdict[l]
                self.neutralsdict.setdefault(l)
                self.neutralsdict[l] = newneutralsdict[l]
            else :
                for gate in self.gates:
                    gate.operanddict.setdefault(l)
                    gate.proofdict.setdefault(l)
                    gate.valuedict.setdefault(l)

    def removeLevels(self,levelsdict):
        ''' Assuming levelsdict is a dictionnary with 3 keys namely
            'inputs'
            'ouptuts'
            'rest'
            each key contains a tuple of levels to be removed of each section.

            For example, levelsdict =
               {'inputs':('ciphertext','message')
                'outputs':('commitment')
                'rest': ('message','opening')}
        '''

        for gate in self.inputs :
            gate.remove(levelsdict['inputs'])
        for gate in self.outputs :
            gate.remove(levelsdict['outputs'])
        for gate in self.gates:
            if not gate in self.inputs and not gate in self.outputs:
                gate.remove(levelsdict['rest'])

    def copy(self):
        newinputs = []
        newgates = []
        newoutputs = []
        for gate in self.gates :
            newgate = gate.copy()
            newgates.append(newgate)
            if gate in self.inputs :
                newinputs.append(newgate)
            if gate in self.outputs :
                newoutputs.append(newgate)

        return Circuit(newinputs,newoutputs,newgates,self.label,self.operandsdict.copy(),self.neutralsdict.copy())

class Gate:

    def __init__(self,inputs = None,label=None, operandname = None, operanddict={}, valuedict={}, proofdict={}):

        self.inputs = inputs
        self.valuedict = valuedict
        self.operandname = operandname
        self.operanddict = operanddict
        self.label = label
        self.proofdict = proofdict
        self.gates = [self]

    def __str__(self):
        s=""
        v=""
        for val in self.valuedict :
                v = v+"=> "+str(val)+" : "+str(self.valuedict[val])+"\n"
        if not self.inputs == None :
            for inp in self.inputs :
                s = s+"Gate ["+str(inp.label)+"]\n"
            return str(len(self.inputs))+"-Gate "+str(self.operandname)+" ["+str(self.label)+"] with value(s) :\n"+v+"\n"+"and Inputs :\n"+s+"\n"
        else :
            return "Gate ["+str(self.label)+"] with value(s) :\n"+ v+"\n"

    def __repr__(self):
        if self.inputs == None :
            a = 0
        else :
            a = len(self.inputs)
        s = str(a)+'-Gate '+str(self.label)
        return s

    def copy(self):
        if not self.inputs == None :
            newinputs = self.inputs+[]
        else :
            newinputs = None
        return Gate(newinputs, self.label, self.operandname, self.operanddict.copy(),self.valuedict.copy(),self.proofdict.copy())

    def remove(self,levellist):
        for level in levellist :
            if level in self.operanddict :
                self.operanddict.pop(level)
            if level in self.valuedict :
                self.valuedict.pop(level)
            if level in self.proofdict :
                self.proofdict.pop(level)

    def compute(self,levels):
        ''' This method computes if possible the value of the gate on each level of
        levels. Note that the operations needed to compute the gate are stored in
        the dictionary self.operanddict
        '''
        for l in levels :
            if l in self.operanddict :
                if not l in self.proofdict:
                    inputsvalueslist = []
                    for inputgate in self.inputs :
                        inputsvalueslist.append(inputgate.valuedict[l])
                    if not None in inputsvalueslist :
                        self.valuedict[l] = self.operanddict[l](*inputsvalueslist)
                elif self.proofdict[l] == None :
                    inputsvalueslist = []
                    for inputgate in self.inputs :
                        inputsvalueslist.append(inputgate.valuedict[l])
                    if not None in inputsvalueslist :
                        # in case there is a proof, the value has to be computed in another way
                        self.valuedict[l] = self.operanddict[l](*inputsvalueslist)
                elif self.proofdict[l] == 'tag' or not self.proofdict[l] == None :
                    getarguments, performproof = self.operanddict[l]
                    arguments = getarguments(self)
                    performproof(*arguments)

class Worker:
    def __init__(self, publicKey, secretKey,circuit=None, clientsList=[], args={}):
        ''' - circuit is a circuit where each input gate contains
            a) on level 'commitment' : a commitment to some message m
            b) on level 'ciphertext' : a ciphertext encrypting message m
            c) on level 'consist' : a consitency proof on the commitment and the encyption
            d) on level 'verif' : a verifiability proof on the commitment
            - publickey is the key used to encrypt and commit to messages
            - secretKey is used to decrypt messages
        '''
        self.circuit = circuit
        self.publicKey = publicKey
        self.secretKey = secretKey
        self.clientsList = clientsList
        self.args = args # possibly a dictionnary containing a list of precomputed multiplication commitment triplets

    def decryptInputs(self,labellist = []):
        ''' Assuming each input gate contains a ciphertext and a (consistent)
        commitment, this method decrypt all the ciphertexts using the self.secretKey
        and place the decryptions in a new level called 'message'. Also it places
        the openings of the commitment in level 'opening'. Finally it creates a level
        'openingclear' to possibly store the opening in clear (or the randomness
        used in the opening if the opening is an element of the group for example).
        '''

        if labellist == [] :
            for inputgate in self.circuit.inputs :
                enc = inputgate.valuedict['ciphertext']
                dec = self.secretKey.decrypt(enc)
                assert not dec == None # ERROR in decrypting ciphertext (possible too high messacge),check the proof
                o = self.secretKey.opens(enc)
                inputgate.valuedict['message'] = dec
                inputgate.valuedict['opening'] = o

        else :
            for label in labellist :
                for inputgate in self.circuit.inputs :
                    if label in inputgate.label :
                        enc = inputgate.valuedict['ciphertext']
                        dec = self.secretKey.decrypt(enc)
                        o = self.secretKey.opens(enc)
                        inputgate.valuedict['message'] = dec
                        inputgate.valuedict['opening'] = o

    def evalClearCircuit(self):
        self.circuit.compute(['message','opening','openingclear'])

    def sendCircuit(self,circuit):
        for client in self.clientsList :
            client.updateCircuit(circuit)

    def sendArguments(self,label = '', *args):
        for client in self.clientsList :
            client.getArguments(label,*args)
    """
    def getSignatureSet(self,filename):
        pubkey = self.publicKey
        pubparam = pubkey.PPATSpp

        sigSet = signatureSet(pubparam,pubkey)
        sigSet.loadSignatureSet(filename)

        return sigSet
    """

    def tagproofGate(self,levels,operations):
        ''' This method is used to tag some gates containing one operation of the
        list operations in order to prevent the evaluation algorithms to
        evaluate the gates. It do so on each level of the list levels.
        The tagging consists to set the proofdict[level] of the gate to 'tag'.
        '''
        for gate in self.circuit.gates :
            for l in levels :
                if not gate.operandname == None :
                    if gate.operandname in operations[l]:
                        gate.proofdict[l] = 'tag'

    def checkInputsProofs(self,proofCheckOperations,printing = False):
        ''' This method is used to check the correctness of the proofs contained on
        each input gate for each level of proofCheckOperations. For example, the consistency proof of the CCE and the
        verifiability proof of the commtment.
        proofCheckOperations is a dictionnary where keys are levels and
        the items a 2-uple methods (getarguments,performproof)
             getarguments on input a gate, returns the arguments needed to perform
                the proof checking of the level
            performproof on input some arguments perform a proof and return True or
               False if the proof is correct or not

        The method returns a list containing the input gates for which the proof on
        some level(s) did not succeed.
        '''
        wrongproofslist = []
        for l in proofCheckOperations :
            if printing : print "checking ", str(l)
            for inputgate in self.circuit.inputs :
                if l in inputgate.proofdict:
                    if printing : print "\t checking gate",str(inputgate.operandname)," ",str(inputgate.label)
                    getarguments, performproof = proofCheckOperations[l]
                    arguments = getarguments(inputgate)
                    result = performproof(*arguments)
                    if printing : print "\t proof is correct : ",result
                    if not result :
                        wrongproofslist.append((inputgate,l))
            if printing : print "level ", str(l), "done"

        return wrongproofslist

    def recommitInputs(self,labellist):
        '''
           This method computes new commitments for each input gate. The new commit-
           ments commit on the exact same value as the initial commitments.
           The method provides a proof of correctness for each translation

           The goal for the worker in doing this is to obtain commitments for wich
           she knows the randomnessed used in the openings (which is not the case for
           the commitments submitted by the clients in the ppats).
        '''
        gatelist = []
        for l in labellist :
            for g in self.circuit.inputs :
                if l in g.label :
                    c = g.valuedict['commitment']
                    m = g.valuedict['message']
                    a = g.valuedict['opening']
                    clist = nizk.splitCommitment(self.publicKey,c,m,a)
                    A,B = clist
                    m1,r1,a1,com1 = A
                    m2,r2,a2,com2 = B

                    vd = {'commitment':com1,'opening':a1,'message':m1,'openingclear':r1}
                    pd = {'recommitProof':(0,a2,com2)}
                    g2 = Gate([g],'recommitedInput',valuedict = vd, proofdict = pd)

                    gatelist.append(g2)
        self.circuit.gates = self.circuit.gates + gatelist

    def computeProofs(self,proofOperationsDict,gates=None,checkinputs = False):
        '''
           -  proofOperationsDict is a dictionnary where keys are names of operations
           for which a proof has to be computed (e.g. 'add','mul',...)
           The items corresponding to the keys are two functions :
               - getarguments(gate) : provide the arguments needed for the proof
               - performproof(gate,*arguments) : compute the proof for the gate and
               store it in the proofdict of the gate
        '''
        if gates == None :
            gates = self.circuit.gates
        for g in gates :
            if not checkinputs and g in self.circuit.inputs :
                pass
            elif (checkinputs and g in self.circuit.inputs) or not g in self.circuit.inputs :
                        if g.operandname in proofOperationsDict :
                            getarguments, performproof = proofOperationsDict[g.operandname]
                            arguments = getarguments(g)
                            performproof(g,*arguments)

class Client:
    def __init__(self,publicKey,label,circuit=None,argsdict={}):
        self.circuit = circuit
        self.publicKey = publicKey
        self.label = label # Client's ID
        self.inputsSendDict = None
        self.addInputsSend()
        self.argsdict = argsdict

    def __str__(self):
        return "Client "+self.label

    def updateCircuit(self,newcircuit):
        self.circuit = newcircuit

    def addInputsSend(self,arg=None):
        ''' Add an element to the dictionnary self.inputsSendDict
        '''
        if arg == None and self.inputsSendDict == None :
            self.inputsSendDict = {}
        elif arg == None :
            pass
        else :
            k = len(self.inputsSendDict)
            self.inputsSendDict[k] = arg
    def getCCEInput(self):
        return None

    def getArguments(self,label = '',*args):

        if not label == '' :
            self.argsdic[label]= args
        else :
            self.argsdic[len(self.argsdict)]= args

    def checkCircuitProofs(self,proofCheckOperationsDict,checkingMyself = True,printing = False):
        ''' This method is used to check the correctness of the proofs contained on
        each gate for each set : inputs, outputs and the rest.

        proofCheckOperationsDict is a dictionnary containing 4 keys :
            'inputs', 'outputs', 'rest' and 'myself'

            each corresponding item to these keys contains another dictionnary
            where the entries are levels for which a proof has to be verified (for
            example a multiplicative proof on the level 'mulproof')
            an item is a 2-uple of functions :
                - getarguments describes how to get the arguments of the proof from
                the gate
                - performproof is the proof to be performed ont the previous arguments

        the boolean value checkingMyself :
            - True : a specific verification for the gate(s) sent by the client
            - False : all the gates are verified equally

        '''

        wrongproofslist = []
        for i in range(len(self.circuit.gates)) :
            gate = self.circuit.gates[i]
            #t01 = time.time()
            if gate in self.circuit.inputs :
                key = 'input'
            elif gate in self.circuit.outputs :
                key = 'output'
            else :
                key = 'other'
            st = key
            if str(self) in gate.label and checkingMyself:
                st = 'my '+st
                key = 'my'
            gateChecked = False

            for l in proofCheckOperationsDict[key] :
                condition, getarguments, performproof = proofCheckOperationsDict[key][l]
                if condition(gate):
                    if printing : print "checking",st,"gate",str(gate.label),'at position', i,"with key proof",str(l)
                    arguments = getarguments(gate)
                    result = performproof(*arguments)
                    gateChecked = True
                    if printing : print "\t proof is correct :",result
                    if not result :
                        wrongproofslist.append((gate,l))
            if not gateChecked :
                print 'Gate', repr(gate), 'at position', i,'not checked with key',key

        return wrongproofslist
