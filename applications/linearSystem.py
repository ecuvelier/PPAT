# -*- coding: utf-8 -*-
from protocols.ppatProtocol import Circuit,Gate,Worker,Client
from Crypto.Random.random import randint
import nizkproofs.nizkpok as nizk
import mathTools.invMatrix as iM
import mathTools.field as field
import math
import numpy

class LinearSystemPPATSWorker(Worker):

    def makeCircuit(self):
        inputs = []
        for client in self.clientsList :
            inputgate = Gate(label = ('input',str(client)),operandname = '',valuedict={'commitment':None},proofdict={'rangeProof':None})
            inputs.append(inputgate)

        c = Circuit(inputs=inputs,outputs = [], gates=inputs,label = "Linear System")

        self.circuit = c

    def fillInputGates(self,maxexp,printing=False):
        self.maxexp = maxexp
        for i in range(len(self.clientsList)) :
            client = self.clientsList[i]
            inputgate = self.circuit.inputs[i]
            e,cproof,mproof = client.getCCEInput(self.maxexp)
            c = self.publicKey.derivCom(e)
            inputgate.valuedict['commitment'] = c
            inputgate.valuedict['ciphertext'] = e
            inputgate.proofdict['consist'] = cproof
            inputgate.proofdict['rangeProof'] = mproof
            if printing : print "input of",str(client),"received"

    def recomInputs(self):
        self.recommitInputs(['input'])
        for g in self.circuit.gates :
            if 'recommitedInput' in g.label :
                inputgate = g.inputs[0]
                clientId = inputgate.label[1]
                g.label = ('recommitedInput',clientId)

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

    def solveSystem(self,B=None,printing=False):
        def findFactor(n):
            a = int(math.ceil(math.sqrt(n)))
            b = int(math.floor(math.sqrt(n)))

            while not a==0 or not b==0 :
                c = int(n/a)
                if c*a == n:
                    return c,a
                else :
                    a -= 1
                d = int(n/b)
                if d*b == n:
                    return d,b
                else :
                    d += 1

        l = len(self.clientsList)
        m,n = findFactor(l)
        Fp = self.publicKey.PPATSpp.h.ECG.F
        mList = []
        comList = []
        randList = []
        for g in self.circuit.gates :
            if 'recommitedInput' in g.label :
                mes = g.valuedict['message']
                com = g.valuedict['commitment']
                rand = g.valuedict['openingclear']
                mList.append(field.FieldElem(mes,Fp))
                comList.append(com)
                randList.append(rand)
        tempL = numpy.array(mList,dtype=object)
        tempcomL = numpy.array(comList,dtype=object)
        temprandL = numpy.array(randList,dtype=object)
        #print tempL,len(tempL)
        #assert k == len(tempL)
        self.A = numpy.reshape(tempL,(m,n)) # matrix to invert
        self.D = numpy.reshape(tempcomL,(m,n)) # same matrix on commitments
        self.R = numpy.reshape(temprandL,(m,n)) # same matrix on openings
        if printing :
            print 'rectangular decomposition of the number of clients', l, 'is', m,',',n,', this is the size of matrix A:\n',self.A

        zero = Fp.zero()
        one = Fp.one()
        Id = iM.eye(m,zero,one)
        C,self.Ainv,b = iM.invertmatrix(self.A,Id,zero,one) # D is the inverse matrix of A
        if printing : print 'the inverse of A is :',self.Ainv
        assert iM.equal(C,Id) is True
        assert b is True
        assert iM.equal(numpy.dot(self.A,self.Ainv),Id) is True
        if B == None :
            B = numpy.zeros(m,dtype=object)# array containing the public independent coefficients
            for i in range(len(B)):
                B[i] = randint(0,2**self.maxexp)

        Z = numpy.dot(self.Ainv,B) # Solution of the system of size (m,1)
        v = {'solution':Z,'matrixsize':(m,n)}
        gate = Gate(label=('output','solution'),valuedict = v)
        self.circuit.outputs.append(gate)
        self.circuit.gates.append(gate)
        #ZCom = Z.copy()
        #ZOpe = Z.copy()
        #for j in range(n):
            #Zj = ZCom[j]
            #comZj,rj = self.publicKey.commit(Zj)
            #ZCom[j] = comZj
            #ZOpe[j] = rj

        for i in range(m):
            mBpi = 0
            comBpi,rBpi = self.publicKey.commit(0,0)
            order = self.publicKey.PPATSpp.order
            for j in range(n):
                mBpi = (mBpi+Z[j].val*self.A[i][j].val)%order
                comBpi = comBpi+self.D[i][j]*(Z[j].val%order)
                rBpi = (rBpi+self.R[i][j]*Z[j].val)%order
            assert self.publicKey.verifyCommitment(comBpi,mBpi,rBpi) is True
            v = {'message':mBpi,'commitment':comBpi,'openingclear':rBpi}
            gate = Gate(label=('output','opening row',str(i)),valuedict = v)
            self.circuit.outputs.append(gate)
            self.circuit.gates.append(gate)
            self.Z = Z



class LinearSystemPPATSClient(Client):

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

    def checkLSCircuitProofs(self,printing=False):

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

        def condmygate(gate):
            return (str(self) in gate.label) and gate in self.circuit.inputs
        def getcommitment(gate):
            com = gate.valuedict['commitment']
            return (com,)
        def checkmygate(com):
            return com in self.inputsSendDict['com'].values()

        def condsolgate(gate):
            return 'solution' in gate.label
        def getsolarg(gate):
            openingList = []
            for g in self.circuit.outputs :
                if 'solution' in g.label:
                    Z = g.valuedict['solution']
                    m,n = g.valuedict['matrixsize']
                else :
                    a,b,c = g.label
                    openingList.append((c,g.valuedict))
            openingList.sort()
            return Z,m,n,openingList
        def checkSolution(Z,m,n,openingList):
            comList = []
            for g in self.circuit.gates :
                if 'recommitedInput' in g.label :
                    com = g.valuedict['commitment']
                    comList.append(com)
            tempcomL = numpy.array(comList,dtype=object)
            D = numpy.reshape(tempcomL,(m,n)) # matrix on commitments
            res1 = True
            for i in range(m):
                comBpi,r = self.publicKey.commit(0,0)
                order = self.publicKey.PPATSpp.order
                for j in range(n):
                    comBpi = comBpi+D[i][j]*(Z[j].val%order)
                oi = openingList[i]
                mi = oi[1]['message']
                ri = oi[1]['openingclear']
                res1 = res1 and self.publicKey.verifyCommitment(comBpi,mi,ri)
            return res1


        proofCheckOperationsDict = {'input':{'rangeProof':(condRangeproof,getargRangeproof,checkRangeproof)},'output':{'solution':(condsolgate,getsolarg,checkSolution)},'other':{'recomProof':(condRecomProof,getargRecomProof,checkRecomProof)},'my':{'checkmygate':(condmygate,getcommitment,checkmygate)}}
        return self.checkCircuitProofs(proofCheckOperationsDict,printing=printing)


