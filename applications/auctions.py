# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

'''
The following script defines a worker that gets from each client an input which is a
CCE of a number between 0 and 2**16.
The worker will then compute the sorted list of the commitments and publish it
together with the proofs attached.
Each client can then check the validity of the proofs.
'''
from protocols.ppatProtocol import Circuit,Gate,Worker,Client
from Crypto.Random.random import randint
import nizkproofs.nizkpok as nizk
#import ppat.ppats as ppats


class AuctionsPPATSWorker(Worker):

    def makeCircuit(self):
        inputs = []
        for client in self.clientsList :
            inputgate = Gate(label = ('input',str(client)),operandname = '',valuedict={'commitment':None},proofdict={'rangeProof':None})
            inputs.append(inputgate)

        c = Circuit(inputs=inputs,outputs = [], gates=inputs,label = "Sorting")

        self.circuit = c

    def fillInputGates(self,printing=False):
        for i in range(len(self.clientsList)) :
            client = self.clientsList[i]
            inputgate = self.circuit.inputs[i]
            e,cproof,mproof = client.getCCEInput()
            c = self.publicKey.derivCom(e)
            inputgate.valuedict['commitment'] = c
            inputgate.valuedict['ciphertext'] = e
            inputgate.proofdict['consist'] = cproof
            inputgate.proofdict['rangeProof'] = mproof
            if printing : print "input of",str(client),"received"

    def decryptAndCheckProofs(self,printing=False):
        self.decryptInputs()
        def getargconsistproof(gate):
            cce = gate.valuedict['ciphertext']
            consistproof = gate.proofdict['consist']
            return cce, consistproof
        def checkconsistproof(cce,consistproof):
            return nizk.consistencyProofCheck(self.publicKey,cce,consistproof)
        def getargrangeproof(gate):
            com = gate.valuedict['commitment']
            rproof = gate.proofdict['rangeProof']
            return com,rproof
        def checkrangeproof(com,rproof):
            return True in nizk.base2RangeProofCheck(self.publicKey,com,rproof)

        proofCheckOperations = {'consist':(getargconsistproof,checkconsistproof),'rangeProof':(getargrangeproof,checkrangeproof)}
        return self.checkInputsProofs(proofCheckOperations,printing)

    def recomInputs(self):
        self.recommitInputs(['input'])
        for g in self.circuit.gates :
            if 'recommitedInput' in g.label :
                inputgate = g.inputs[0]
                clientId = inputgate.label[1]
                g.label = ('recommitedInput',clientId)

    def sort(self,printing = False):
        L = []
        for g in self.circuit.gates :
            if 'recommitedInput' in g.label :
                m = g.valuedict['message']
                L.append((m,g))
        L.sort()
        L.reverse()
        tempoutputs = []

        for m,gate in L :
            #ngate = gate.copy()
            #a,b = ngate.label
            #ngate.label = ('output',b)
            #ngate.inputs = [gate]
            tempoutputs.append(gate)


        #outputs = tempoutputs
        outputs = []
        #order = self.publicKey.PPATSpp.order
        maxexp = self.publicKey.maxexp

        for i in range(len(tempoutputs)-1):
            currentgate = tempoutputs[i]
            nextgate = tempoutputs[i+1]
            currentm = currentgate.valuedict['message']
            nextm = nextgate.valuedict['message']
            currentcom = currentgate.valuedict['commitment']
            nextcom = nextgate.valuedict['commitment']
            currentopening = currentgate.valuedict['openingclear']
            nextopening = nextgate.valuedict['openingclear']

            #newm = (nextm-currentm)%order
            newcom = nextcom-currentcom
            newopening = nextopening-currentopening
            geqPr = nizk.geqProof(self.publicKey,currentcom,currentm,currentopening,nextcom,nextm,nextopening,maxexp)

            newvaluedict = {'commitment':newcom,'openingclear':newopening}
            newproofdict = {'geqproof':geqPr}
            newgate = Gate([nextgate,currentgate],('output',str(i)),'sub',valuedict=newvaluedict,proofdict=newproofdict)
            outputs.append(newgate)
            if printing : print "gate sub ",str(i)," added"

        self.circuit.outputs = outputs
        self.circuit.gates = self.circuit.gates + outputs

class AuctionsPPATSClient(Client):

    def getCCEInput(self,maxexp=16):
        self.maxexp = maxexp
        constraint = 2**self.maxexp
        m = randint(0,constraint)
        r = self.publicKey.random()
        cce, cproof = self.publicKey.encryptwithCproof(m,r)
        com = self.publicKey.derivCom(cce)
        mproof = nizk.base2RangeProof(self.publicKey,com,m,r,maxexp,False)
        self.addInputsSend((cce,com,cproof,mproof))

        return cce,cproof,mproof

    def addInputsSend(self,arg=None):
        if arg == None and self.inputsSendDict == None :
            self.inputsSendDict = {'all':{},'com':{}}
        elif arg == None :
            pass
        else :
            k = len(self.inputsSendDict['all'])
            cce,com,cproof,mproof = arg
            self.inputsSendDict['all'][k] = (cce,cproof,mproof)
            self.inputsSendDict['com'][k] = com

    def checkAuctionsCircuitProofs(self,printing=False):

        def condRecomProof(gate):
            return 'recommitProof' in gate.proofdict
        def getargRecomProof(gate):
            com1 = gate.inputs[0].valuedict['commitment']
            com2 = gate.valuedict['commitment']
            recomproof = gate.proofdict['recommitProof']
            return com1,com2, recomproof
        def checkRecomProof(com1,com2,recomproof):
            m3, o3, com3 = recomproof
            res1 = m3 == 0
            res2 = self.publicKey.verifyOpening(com3,m3,o3)
            res3 = com1 == com2+com3
            return res1 and res2 and res3

        def condRangeproof(gate):
            return 'rangeProof' in gate.proofdict

        def getargRangeproof(gate):
            if 'rangeProof' in gate.proofdict :
               com = gate.valuedict['commitment']
               rproof = gate.proofdict['rangeProof']
               return com,rproof
            else :
                return None,None
        def checkRangeproof(com,rproof):
            if not com==None and not rproof==None :
                return True in nizk.base2RangeProofCheck(self.publicKey,com,rproof)
            else :
                return True

        def condGeqproof(gate):
            return gate.operandname == 'sub'

        def getargGeqproof(gate):
            com0 = gate.inputs[0].valuedict['commitment']
            com1 = gate.inputs[1].valuedict['commitment']
            geqproof = gate.proofdict['geqproof']
            return com0,com1,geqproof

        def checkGeqproof(com0,com1,geqproof):
            return nizk.geqProofCheck(self.publicKey,com0,com1,geqproof,self.maxexp)

        def getargsubproof(gate):
            com = gate.valuedict['commitment']
            com0 = gate.inputs[0].valuedict['commitment']
            com1 = gate.inputs[1].valuedict['commitment']
            return com,com0,com1

        def checksubproof(com,com0,com1):
            comp = com.addOptim(com1)
            return comp == com0

        def condmygate(gate):
            return (str(self) in gate.label) and gate in self.circuit.inputs
        def getcommitment(gate):
            com = gate.valuedict['commitment']
            return (com,)
        def checkmygate(com):
            return com in self.inputsSendDict['com'].values()


        proofCheckOperationsDict = {'input':{'rangeProof':(condRangeproof,getargRangeproof,checkRangeproof)},'output':{'geqproof':(condGeqproof,getargGeqproof,checkGeqproof),'subproof':(condGeqproof,getargsubproof,checksubproof)},'other':{'recomProof':(condRecomProof,getargRecomProof,checkRecomProof)},'my':{'checkmygate':(condmygate,getcommitment,checkmygate)}}
        return self.checkCircuitProofs(proofCheckOperationsDict,printing=printing)
