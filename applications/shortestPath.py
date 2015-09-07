# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

from protocols.ppatProtocol import Circuit,Gate,Worker,Client
import tools.simplegraph as sg
from Crypto.Random.random import randint
import random as rd
import nizkproofs.nizkpok as nizk

class SPWorker(Worker):
    def makeCircuit(self,numberOfEdges):
        infexp = self.args['max_exp_message_w']
        inf = 2**infexp
        V,E,M1 = sg.createCGraph(numberOfEdges)
        M = M1.copy()
        k = len(V) #number of veritces, size of M (sq matrix)
        inputsg = []
        counter = 0
        for i in range(k):
            for j in range(k):
                if M[i,j] == 1 :
                    client = self.clientsList[counter]
                    counter = counter+1
                    inputgate = Gate(label = ('input',str(client)),operandname = '',valuedict={'commitment':None},proofdict={'rangeProof':None})
                    inputsg.append(inputgate)
                    M[i,j] = 'Edge of '+str(client)

        assert counter == len(self.clientsList)

        com0,r0 = self.publicKey.commit(0)
        cominf,rinf = self.publicKey.commit(inf)

        weightsOfVertices = []
        verticesList = []
        predecessorsList = []

        for i in range(k):
            if i == 0 :
                sourceGate = Gate(label=('vertex','0'),operandname = '',valuedict = {'commitment':com0,'message':0,'openingclear': r0})
                verticesList.append(sourceGate)
                weightSourceGate = Gate(label=('vertexweight','0'),operandname = '',valuedict = {'commitment':com0,'message':0,'openingclear': r0})
                weightsOfVertices.append(weightSourceGate)
                predSourceGate = Gate(label=('predecessor','0'),operandname = '',valuedict = {'commitment':com0,'message':0,'openingclear': r0})
                predecessorsList.append(predSourceGate)
            else :
                compi,rpi = self.publicKey.commit(i)
                vertexGate = Gate(label=('vertex',str(i)),operandname = '',valuedict = {'commitment':compi,'message':i,'openingclear': rpi})
                verticesList.append(vertexGate)
                weightGate = Gate(label=('vertexweight',str(i)),operandname = '',valuedict = {'commitment':cominf,'message':inf,'openingclear': rinf})
                weightsOfVertices.append(weightGate)
                predGate = Gate(label=('predecessor',str(i)),operandname = '',valuedict = {'commitment':compi,'message':i,'openingclear': rpi})
                predecessorsList.append(predGate)


        inputs = inputsg+verticesList+weightsOfVertices+predecessorsList

        c = Circuit(inputs=inputs,outputs = [], gates=inputs,label = "Shortest Path")

        self.args['adjMatrix'] = M
        self.args['adjMatrixClear'] = M1
        self.args['edgesList'] = inputsg
        self.args['verticesList'] = verticesList
        self.args['weightsOfVertices'] = weightsOfVertices
        self.args['predecessorsList'] = predecessorsList

        self.circuit = c

    def produceMultiplicationTriplets(self,k):
        tripletsclear = []
        triplets = []
        for i in range(k):
            m1 = self.publicKey.random()
            m2 = self.publicKey.random()
            m3 = m1*m2
            com1, r1 = self.publicKey.commit(m1)
            com2, r2 = self.publicKey.commit(m2)
            com3, r3 = self.publicKey.commit(m3)
            a = (m1,r1,com1),(m2,r2,com2),(m3,r3,com3)
            b = com1,com2,com3
            tripletsclear.append(a)
            triplets.append(b)
        self.args['triplets'] = triplets
        self.args['tripletsclear'] = tripletsclear

    def assignTriplets(self,patern=None):
        tripletsclear = self.args['tripletsclear']
        triplets = self.args['triplets']
        mulgates = []
        for gate in self.circuit.gates :
            if gate.operandname == 'mul' :
                mulgates.append(gate)
        if patern == None:
            L = range(len(tripletsclear))
            rd.shuffle(L)
            patern = L

        for i in range(len(mulgates)):
            gate  = mulgates[i]
            j = patern[i]
            if gate.proofdict['commitment'] == 'tag' :
                gate.proofdict['commitment'] = {}
            A,B,C = tripletsclear[j]
            (m1,r1,com1),(m2,r2,com2),(m3,r3,com3) = A,B,C
            gate.proofdict['triplet'] = com1,com2,com3
            gate.proofdict['tripletOpenings'] = m1,m2,r1,r2,r3
            tripletsclear[j] = A,B,C, 'used in ',gate
            triplets[j] = triplets[j]+('used in ',gate,)
        self.args['triplets'] = triplets
        self.args['tripletsclear'] = tripletsclear

    def fillInputGates(self,printing=False):
        for k in range(len(self.clientsList)) :
            client = self.clientsList[k]
            clientInput = client.getCCEInput()
            e,cproof,rproof = clientInput
            c = self.publicKey.derivCom(e)
            inputgate = self.circuit.inputs[k]
            assert 'input' in inputgate.label
            inputgate.valuedict['commitment'] = c
            inputgate.valuedict['ciphertext'] = e
            inputgate.proofdict['consistProof'] = cproof
            inputgate.proofdict['rangeProof'] = rproof
            if printing : print "input of",str(client),"received"

    def decryptAndCheckProofs(self,printing=False):

        self.decryptInputs(labellist = ['input'])

        def getargconsistproof(gate):
            cce = gate.valuedict['ciphertext']
            consistproof = gate.proofdict['consistProof']
            return cce, consistproof
        def checkconsistproof(cce,consistproof):
            return nizk.consistencyProofCheck(self.publicKey,cce,consistproof)

        def getargrangeproof(gate):
            com = gate.valuedict['commitment']
            rproof = gate.proofdict['rangeProof']
            return com,rproof
        def checkrangeproof(com,rproof):
            return True in nizk.base2RangeProofCheck(self.publicKey,com,rproof)

        proofCheckOperations = {'consistProof':(getargconsistproof,checkconsistproof),'rangeProof':(getargrangeproof,checkrangeproof)}
        return self.checkInputsProofs(proofCheckOperations,printing)

    def recomInputs(self):
        self.recommitInputs(['input'])
        edgesList = []
        for g in self.circuit.gates :
            if 'recommitedInput' in g.label :
                edgesList.append(g)
        self.args['edgesList'] = edgesList


    def computeShortestPath(self):
        order = self.publicKey.PPATSpp.order

        #defining operations
        def add(x,y):
            return x+y
        def mul(x,y):
            return x*y
        def argmulcom(gate):
            return gate,gate.inputs[0],gate.inputs[1]
        def mulcom(gate,inputgate1,inputgate2):

            a1,a2,a3 = gate.proofdict['triplet']
            ma1,ma2,oa1,oa2,oa3 = gate.proofdict['tripletOpenings']

            m1 = (inputgate1.valuedict['message'])%order
            m2 = (inputgate2.valuedict['message'])%order

            o1 = (inputgate1.valuedict['openingclear'])
            o2 = (inputgate2.valuedict['openingclear'])

            if o1 == None :
                self.circuit.compute(['openingclear','commitment'],[inputgate1])
                o1 = (inputgate1.valuedict['openingclear'])
            if o2 == None :
                self.circuit.compute(['openingclear','commitment'],[inputgate2])
                o2 = (inputgate2.valuedict['openingclear'])
            o1=o1%order
            o2=o2%order

            tm1 = m1-ma1
            tm2 = m2-ma2
            to1 = o1-oa1
            to2 = o2-oa2
            #assert self.publicKey.verifyCommitment(com1-a1,tm1,to1)
            #assert self.publicKey.verifyCommitment(com2-a2,tm2,to2)
            openings = (tm1,to1),(tm2,to2)
            com3 = self.publicKey.multiplicationCommitFromTriplet(a1,a2,a3,tm1,tm2)
            r3 = (m1*oa2+m2*oa1-ma2*oa1-ma1*oa2+oa3)%order

            gate.valuedict['commitment'] = com3
            gate.valuedict['openingclear'] = r3
            #assert self.publicKey.verifyCommitment(com3,m3,r3)
            gate.proofdict['mulProof'] = openings

        def sub(x,y):
            return x-y
        def cond(x):
            return int(x<0)
        def argcondcom(gate):
            return gate, gate.inputs[0]
        def condcom(gate,inputgate):
            self.circuit.compute(['openingclear','commitment'],[inputgate])
            com = inputgate.valuedict['commitment']
            m = inputgate.valuedict['message']
            r = inputgate.valuedict['openingclear']
            maxexp = self.args['max_exp_message_w']
            cl1, cl2 = nizk.gtzero(self.publicKey,com,m,r,maxexp) #TODO : Check this out
            #assert self.publicKey.base2RangeProofCheck(com,cl2)
            m1 = cl1[0][0]
            r1 = cl1[0][1]
            com1 = cl1[0][3]
            gate.valuedict['message'] = m1
            gate.valuedict['openingclear'] = r1
            gate.valuedict['commitment'] = com1
            gate.proofdict['rangeProof'] = cl2

        adddict = {'message':add,'openingclear':add,'commitment':add}
        subdict = {'message':sub,'openingclear':sub,'commitment':sub}
        muldict = {'message':mul,'commitment':(argmulcom,mulcom)}
        conddict = {'message':cond,'commitment':(argcondcom,condcom)}

        vdict = {'commitment':None,'message':None,'opening':None,'openingclear':None}
        pdict={'commitment':'tag'}

        M = self.args['adjMatrix']
        wE = self.args['edgesList']
        wV = self.args['weightsOfVertices']
        pV = self.args['predecessorsList']
        V = self.args['verticesList']

        k = len(M) # nb of vertices

        for l in range(k):
            counter = 0
            for i in range(k):
                for j in range(k):
                    if not M[i,j] == 0 :
                        eij = wE[counter]
                        counter = counter+1
                        wvi = wV[i]
                        wvj = wV[j]
                        vi = V[i]
                        pvj = pV[j]
                        addagate = Gate([wvi,eij],label = 'addition Aa'+str(l)+str(i)+str(j)+': w[v'+str(i)+']+w[e'+str(i)+str(j)+']',operandname = 'add',operanddict= adddict.copy(),valuedict = vdict.copy())
                        #
                        subagate = Gate([addagate,wvj],label = 'substraction Sa'+str(l)+str(i)+str(j)+': Aa'+str(i)+str(j)+'-w[v'+str(j)+']',operandname = 'sub',operanddict= subdict.copy(),valuedict = vdict.copy())
                        #
                        condgate = Gate([subagate],label = 'Condition C'+str(l)+str(i)+str(j)+': Sa'+str(i)+str(j)+'< 0',operandname = 'cond',operanddict= conddict.copy(),valuedict = vdict.copy(),proofdict = pdict.copy())
                        #
                        mulagate = Gate([condgate,subagate],label = 'multiplication Ma'+str(i)+str(j)+': Sa'+str(i)+str(j)+'*C'+str(i)+str(j),operandname = 'mul',operanddict= muldict.copy(),valuedict = vdict.copy(),proofdict = pdict.copy())
                        #
                        addbgate = Gate([mulagate,wvj],label = 'addition Ab'+str(l)+str(i)+str(j)+':  w[v'+str(j)+']+Ma'+str(i)+str(j),operandname = 'add',operanddict= adddict.copy(),valuedict = vdict.copy())
                        #
                        subbgate = Gate([vi,pvj],label = 'substraction Sb'+str(l)+str(i)+str(j)+': v'+str(i)+'-p[v'+str(j)+']',operandname = 'sub',operanddict= subdict.copy(),valuedict = vdict.copy())
                        #
                        mulbgate = Gate([condgate,subbgate],label = 'multiplication Mb'+str(l)+str(i)+str(j)+': C'+str(i)+str(j)+'* Sb'+str(i)+str(j),operandname = 'mul',operanddict= muldict.copy(),valuedict = vdict.copy(),proofdict = pdict.copy())
                        #
                        addcgate = Gate([pvj,mulbgate],label = 'addition Ac'+str(l)+str(i)+str(j)+':  p[v'+str(j)+']+Mb'+str(i)+str(j),operandname = 'add',operanddict= adddict.copy(),valuedict = vdict.copy())

                        if l == k-1 :
                            addbgate.label = 'weight of vertex',str(j),'; origin :', addbgate.label
                            addcgate.label = 'predecessor of vertex',str(j),'; origin :', addcgate.label
                        wV[j] = addbgate
                        pV[j] = addcgate
                        self.circuit.gates = self.circuit.gates + [addagate, subagate, condgate, mulagate, addbgate, subbgate, mulbgate, addcgate]
        """
        for k in range(len(wV)) :
            g = wV[k]
            g.label = 'weight of vertex ',str(k),' ; origin : ', g.label
        for k in range(len(pV)) :
            g = pV[k]
            g.label = 'predecessor of vertex ',str(k),' ; origin : ', g.label
        """
        self.circuit.outputs = wV + pV

        self.args['weightsOfVertices'] = wV
        self.args['predecessorsList'] = pV


class SPClient(Client):

    def getCCEInput(self):
        constraint = self.argsdict['max_exp_message_c']
        m = randint(0,2**constraint-1)
        r = self.publicKey.random()
        cce, cproof = self.publicKey.encryptwithCproof(m,r)
        com = self.publicKey.derivCom(cce)
        rproof = nizk.base2RangeProof(self.publicKey,com,m,r,constraint)
        self.addInputsSend((cce,com,cproof,rproof))

        return cce,cproof,rproof

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

    def checkShortesPathCircuitProofs(self,printing=False):

        def condRangeProof(gate):
            return 'rangeProof' in gate.proofdict
        def getargRangeProof(gate):
            com = gate.valuedict['commitment']
            rproof = gate.proofdict['rangeProof']
            return com,rproof
        def checkRangeProof(com,rproof):
            res1 = True in nizk.base2RangeProofCheck(self.publicKey,com,rproof)
            mexp = self.argsdict['max_exp_message_c']
            k = len(rproof)
            res2 = rproof[k-1][0] == 2**(mexp-1)
            for i in range(k-1):
                facti = rproof[i][0]
                res = facti == 2**i
                res2 = res2 and res
            return res1 and res2

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

        def condSubProof(gate):
            return gate.operandname == 'sub'
        def getargSubProof(gate):
            com = gate.valuedict['commitment']
            com0 = gate.inputs[0].valuedict['commitment']
            com1 = gate.inputs[1].valuedict['commitment']
            return com,com0,com1
        def condAddProof(gate):
            return gate.operandname == 'add'
        def getargAddProof(gate):
            com = gate.valuedict['commitment']
            com0 = gate.inputs[0].valuedict['commitment']
            com1 = gate.inputs[1].valuedict['commitment']
            return com0,com,com1
        def checkSubAddProof(com,com0,com1):
            comp = com.addOptim(com1)
            return comp == com0

        def condMulProof(gate):
            return gate.operandname == 'mul'
        def getargMulProof(gate):
            com3 = gate.valuedict['commitment']
            com1 = gate.inputs[0].valuedict['commitment']
            com2 = gate.inputs[1].valuedict['commitment']
            triplet = gate.proofdict['triplet']
            mulproof = gate.proofdict['mulProof']
            return com1,com2,com3, triplet, mulproof
        def checkMulProof(com1,com2,com3,triplet,mulproof):
            a1, a2, a3 = triplet
            A,B = mulproof
            ma1,ra1 = A
            ma2,ra2 = B
            res1 = self.publicKey.verifyCommitment(com1-a1,ma1,ra1)
            res2 = self.publicKey.verifyCommitment(com2-a2,ma2,ra2)
            res3 = com3 == self.publicKey.multiplicationCommitFromTriplet(a1,a2,a3,ma1,ma2)
            return res1 and res2 and res3

        def condCondProof(gate):
            return gate.operandname == 'cond'
        def getargCondProof(gate):
            com0 = gate.inputs[0].valuedict['commitment']
            rproof = gate.proofdict['rangeProof']
            com = gate.valuedict['commitment']
            return com0,rproof,com
        def checkCondProof(com0,rproof,com):
            A = rproof[0] #TODO : check here
            res1 = com == A[1]
            res2 = True in nizk.base2RangeProofCheck(self.publicKey,com0,rproof)
            mexp = self.argsdict['max_exp_message_w']
            res3 = True in nizk.base2VerifExpoDecomp(self.publicKey,rproof,mexp)
            return res1 and res2 and res3

        def condOpenOutputProof(gate):
            return gate in self.circuit.outputs
        def getargOOProof(gate):
            m = gate.valuedict['message']
            r = gate.valuedict['openingclear']
            com = gate.valuedict['commitment']
            return com,m,r
        def checkOOProof(com,m,r):
            return self.publicKey.verifyCommitment(com,m,r)

        def condVertexProof(gate):
            return 'vertex' in gate.label
        def getargVertexProof(gate):
            mname = int(gate.label[1])
            m = gate.valuedict['message']
            r = gate.valuedict['openingclear']
            com = gate.valuedict['commitment']
            return mname, m, r, com
        def checkVertexProof(mname,m,r,com):
            res1 = m == mname
            res2 = self.publicKey.verifyCommitment(com,m,r)
            return res1 and res2

        def condVertexweightProof(gate):
            return 'vertexweight' in gate.label
        def getargVertexweightProof(gate):
            mname = int(gate.label[1])
            m = gate.valuedict['message']
            r = gate.valuedict['openingclear']
            com = gate.valuedict['commitment']
            return mname, m, r, com
        def checkVertexweightProof(mname,m,r,com):
            exp = self.argsdict['max_exp_message_w']
            maxfact = 2**exp
            if mname == 0 :
                res1 = m == 0
            else :
                res1 = m == maxfact
            res2 = self.publicKey.verifyCommitment(com,m,r)
            return res1 and res2

        def condPredecessorProof(gate):
            return 'predecessor' in gate.label
        def getargPredecessorProof(gate):
            mname = int(gate.label[1])
            m = gate.valuedict['message']
            r = gate.valuedict['openingclear']
            com = gate.valuedict['commitment']
            return mname, m, r, com
        def checkPredecessorProof(mname,m,r,com):
            res1 = m == mname
            res2 = self.publicKey.verifyCommitment(com,m,r)
            return res1 and res2


        def condmygate(gate):
            return str(self) in gate.label
        def getcommitment(gate):
            com = gate.valuedict['commitment']
            return (com,)
        def checkmygate(com):
            return com in self.inputsSendDict['com'].values()

        allop = {'addProof':(condAddProof,getargAddProof,checkSubAddProof),'subProof':(condSubProof,getargSubProof,checkSubAddProof),'mulProof':(condMulProof,getargMulProof,checkMulProof),'recomProof':(condRecomProof,getargRecomProof,checkRecomProof),'condProof':(condCondProof,getargCondProof,checkCondProof)}

        proofCheckOperationsDict = {'input':{'rangeProof':(condRangeProof,getargRangeProof,checkRangeProof),'vertexProof':(condVertexProof,getargVertexProof,checkVertexProof),'vertexweightProof':(condVertexweightProof,getargVertexweightProof,checkVertexweightProof),'predecessorProof':(condPredecessorProof,getargPredecessorProof,checkPredecessorProof)},'output':{'addProof':(condAddProof,getargAddProof,checkSubAddProof),'openingProof':(condOpenOutputProof,getargOOProof,checkOOProof)},'other':allop,'my':{'checkmygate':(condmygate,getcommitment,checkmygate)}}
        return self.checkCircuitProofs(proofCheckOperationsDict,printing=printing)
