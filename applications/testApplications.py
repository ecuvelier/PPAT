# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

#import circuit
import shortestPath as SP
import auctions
import linearSystem as LS
from script import ppatspk,ppatssk
import math
import gmpy

def testShortestPath(nbClients=16, maxexp=5,printing = False) :
    max_exp_message_clients = maxexp
    ll = int(math.ceil(math.log(nbClients,2)))
    max_exp_message_worker = ll+max_exp_message_clients
    if printing : print 'number of clients :',nbClients,'\n','range size of messages for clients:', 2**max_exp_message_clients,'\n','size of the interval for worker range proofs:',2**max_exp_message_worker
    ad = {'max_exp_message_c':max_exp_message_clients,'max_exp_message_w':max_exp_message_worker}
    cList = []
    for i in range(nbClients) :
        cl = SP.SPClient(ppatspk,str(i),argsdict = ad)
        cList.append(cl)

    W = SP.SPWorker(ppatspk,ppatssk,clientsList = cList, args = ad)
    W.makeCircuit(nbClients)
    nbvertices = len(W.args['verticesList'])
    nbMultTriplets = 2*(nbClients*nbvertices) # 2|E|*|V| multiplications
    W.produceMultiplicationTriplets(nbMultTriplets)
    if printing : print 'receiving inputs'
    W.fillInputGates(printing)
    if printing : print 'decrypting inputs and checking proofs'
    W.decryptAndCheckProofs(printing)
    W.recomInputs()
    if printing : print 'computing shortest path'
    W.computeShortestPath()
    W.assignTriplets()
    W.circuit.compute(['message'])
    W.circuit.compute(['openingclear'],multipass = False,taggatedict = {})
    if printing : print 'computing shortest path proofs'
    W.circuit.compute(['commitment'])
    W.circuit.compute(['openingclear'])

    allbutcommitment = ('ciphertext','message','opening','openingclear')
    allbutMOC = ('ciphertext','opening','consist')
    ldict = {'inputs':(),'outputs':allbutMOC,'rest':allbutcommitment}
    newcirc = W.circuit.copy()
    newcirc.removeLevels(ldict)
    for g in newcirc.inputs :
        if not 'vertex' in g.label and not 'vertexweight' in g.label and not 'predecessor' in g.label:
            g.remove(allbutcommitment)
    W.sendCircuit(newcirc)

    cl0 = cList[0]
    if printing : print 'verifying circuit\'s correctness'
    res = cl0.checkShortesPathCircuitProofs(printing) == []
    if printing : print '\n','Circuit correctly verified :',res

    if printing : print '\n','number of clients (or number of edges) :',nbClients,'\n','number of vertices :',len(W.args['verticesList']),'\n','range size of messages for clients :', 2**max_exp_message_clients,'\n','size of the interval for worker range proofs:',2**max_exp_message_worker
    if printing : print W.args['adjMatrixClear'],'\n'

    return newcirc


def testAuctions(nbClients,printing = False):
    cList = []
    for i in range(0,nbClients):
        cl = auctions.AuctionsPPATSClient(ppatspk,str(i))
        cList.append(cl)

    AWorker = auctions.AuctionsPPATSWorker(ppatspk,ppatssk,clientsList = cList)
    AWorker.makeCircuit()
    AWorker.fillInputGates()
    if printing : print 'inputs received by worker'
    L = AWorker.decryptAndCheckProofs(printing)
    if printing : print 'inputs decrypted and proofs checked by worker'
    AWorker.recomInputs()
    assert L == []
    AWorker.sort()
    if printing : print 'inputs sorted and nizkp proofs prepared by worker'
    ldict = {'inputs':('ciphertext','message','opening','openingclear','consist'),'outputs':('ciphertext','consist','message','opening','openingclear'),'rest':('ciphertext','consist','message','opening','openingclear')}
    newcirc = AWorker.circuit.copy()
    newcirc.removeLevels(ldict)
    AWorker.sendCircuit(newcirc)
    cl0 = AWorker.clientsList[0]
    L = cl0.checkAuctionsCircuitProofs(printing)
    if printing :
        print '\n','Circuit correctly verified :',L==[]
        print 'circuit and proofs checked by client, auctions results are (from highest bid to lowest):'
        for g in newcirc.outputs:
            print g.inputs[1].label[1]

    return newcirc

def testLinearSystem(nbClients,maxexp=16,printing=False):
    assert not gmpy.is_prime(nbClients) is True
    cList = []
    for i in range(0,nbClients):
        cl = LS.LinearSystemPPATSClient(ppatspk,str(i))
        cList.append(cl)
    LSworker = LS.LinearSystemPPATSWorker(ppatspk,ppatssk,clientsList=cList)
    LSworker.makeCircuit()
    LSworker.fillInputGates(maxexp)
    if printing : print 'inputs received by worker'
    L = LSworker.decryptAndCheckProofs(printing)
    if printing : print 'inputs decrypted and proofs checked by worker'
    LSworker.recomInputs()
    if printing : print 'inputs recommited by worker'
    assert L == []
    LSworker.solveSystem(B=None,printing=printing)
    if printing : print 'Linear system solved by worker and proofs prepared'
    ldict = {'inputs':('ciphertext','message','opening','openingclear','consist'),'outputs':('ciphertext','consist'),'rest':('ciphertext','consist','message','opening','openingclear')}
    newcirc = LSworker.circuit.copy()
    newcirc.removeLevels(ldict)
    LSworker.sendCircuit(newcirc)
    cl0 = LSworker.clientsList[0]
    L = cl0.checkLSCircuitProofs(printing)
    assert L == []
    if printing : print 'Solution of the linear System is:\n',LSworker.Z
    return newcirc

