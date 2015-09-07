# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

import unittest
import ppats
from Crypto.Random.random import randint
from script import P,Q, Pair,n
import nizkproofs.nizkpok as nizk

n = int(n)
x1 = randint(1,n-1)
g1 = x1*Q
h1td = randint(1,n-1)
h1 = h1td*P
ppatspp = ppats.PPATSPublicParameters(P,Q,Pair,'Ate', optim = True)
ppatspk = ppats.PPATSPublicKey(ppatspp,g1,h1)
ppatssk = ppats.PPATSPrivateKey(ppatspp,ppatspk,x1)

class TestPPATS(unittest.TestCase):

    def setUp(self):
        self.n = int(n)
        self.maxexp = 16
        self.maxmessage = 2**self.maxexp
        self.ppatspp = ppatspp
        self.ppatspk = ppatspk
        self.ppatssk = ppatssk

    def test_encryption_decryption(self):
        m1 = randint(1,self.maxmessage)
        cipher1 = self.ppatspk.encrypt(m1)
        mp1 = self.ppatssk.decrypt(cipher1)
        self.assertEqual(m1, mp1)

    def test_encrypt_open_verify(self):
        m1 = randint(1,self.maxmessage)
        cipher1 = self.ppatspk.encrypt(m1)
        a1 = self.ppatssk.opens(cipher1)
        self.assertTrue(self.ppatspk.verify(cipher1,m1,a1))

    def test_encrypt_with_consistency_check_proof(self):
        m = randint(1,self.maxmessage)
        c, cproof = self.ppatspk.encryptwithCproof(m)
        self.assertTrue(nizk.consistencyProofCheck(self.ppatspk,c,cproof))

    def test_encrypt_with_verifiability_check_proof(self):
        m = randint(0,1)
        c, vproof = self.ppatspk.encryptwithVproof(m)
        d = self.ppatspk.derivCom(c)
        self.assertTrue(nizk.verifiabilityProofCheck(self.ppatspk,d,vproof))

    def test_encrypt_with_proofs_decrypt_and_check(self):
        m = randint(0,1)
        c,cproof,vproof = self.ppatspk.encryptwithproofs(m)
        d = self.ppatspk.derivCom(c)
        #print 'c',c
        #print 'd',d
        dec = self.ppatssk.decrypt(c)
        self.assertTrue(m==dec)
        self.assertTrue(nizk.consistencyProofCheck(self.ppatspk,c,cproof))
        self.assertTrue(nizk.verifiabilityProofCheck(self.ppatspk,d,vproof))

    def test_addition_of_ciphers(self):
        m1 = randint(1,2**(self.maxexp-1)) # So the addition of the two can be decrytpted
        cipher1 = self.ppatspk.encrypt(m1)
        m2 = randint(1,2**(self.maxexp-1))
        cipher2 = self.ppatspk.encrypt(m2)
        cipher3 = self.ppatspk.encrypt(m1+m2)
        d1 = self.ppatssk.decrypt(cipher1)
        d2 = self.ppatssk.decrypt(cipher2)
        d3 = self.ppatssk.decrypt(cipher3)
        self.assertTrue(d1+d2==d3)

    def test_multiplication_of_cipher_by_scalar(self):
        m1 = randint(1,2**(self.maxexp-10)) # So the multiplication of the cipher can be decrytpted
        cipher1 = self.ppatspk.encrypt(m1)
        a = randint(1,1000)
        cipher2 = self.ppatspk.encrypt(a*m1)
        d1 = self.ppatssk.decrypt(cipher1)
        d2 = self.ppatssk.decrypt(cipher2)
        self.assertTrue(a*d1==d2)

    def test_commitment_and_verify(self):
        m = randint(1,self.n-1)
        r = randint(1,self.n-1)
        com,r = self.ppatspk.commit(m,r)
        self.assertTrue(self.ppatspk.verifyCommitment(com,m,r))

    def test_commitment_and_verify_opening(self):
        m = randint(1,self.n-1)
        r = randint(1,self.n-1)
        com,r = self.ppatspk.commit(m,r)
        o = r*(self.ppatspp.g)
        self.assertTrue(self.ppatspk.verifyOpening(com,m,o))

    def test_addition_of_commitments(self):
        m1 = randint(1,self.maxmessage)
        r1 = randint(1,self.n-1)
        d1,r1 = self.ppatspk.commit(m1,r1)
        m2 = randint(1,self.maxmessage)
        r2 = randint(1,self.n-1)
        d2,r2 = self.ppatspk.commit(m2,r2)
        d3 = d1+d2
        d3p,r3 = self.ppatspk.commit(m1+m2,r1+r2)
        self.assertTrue(d3==d3p)

    def test_multiplication_of_commitment_by_a_scalar(self):
        m1 = randint(1,self.maxmessage)
        r1 = randint(1,self.n-1)
        d1,r1 = self.ppatspk.commit(m1,r1)
        a = randint(1,1000)
        d2 = a*d1
        d2p,r2 = self.ppatspk.commit(a*m1,a*r1)
        self.assertTrue(d2==d2p)

    def test_multiplication_of_commitment_proof_and_check(self):
        m1 = randint(1,self.maxmessage)
        r1 = randint(1,self.n-1)
        d1,r1 = self.ppatspk.commit(m1,r1)
        m2 = randint(1,self.maxmessage)
        r2 = randint(1,self.n-1)
        d2,r2 = self.ppatspk.commit(m2,r2)
        r3 = randint(1,100)
        d3,r3 = self.ppatspk.commit(m1*m2,r3)
        proof = nizk.multiplicationProof(self.ppatspk,d1,d2,d3,m1,m2,r1,r2,r3)
        self.assertTrue(nizk.multiplicationProofCheck(self.ppatspk,d1,d2,d3,proof))

    def test_multiplication_of_commtiments_by_triplet(self):
        #q = self.ppatspp.q
        m1 = randint(1,self.maxmessage)
        r1 = randint(1,self.n-1)
        a1,r1 = self.ppatspk.commit(m1,r1)
        m2 = randint(1,self.maxmessage)
        r2 = randint(1,self.n-1)
        a2,r2 = self.ppatspk.commit(m2,r2)
        r3 = randint(1,self.n-1)
        a3,r3 = self.ppatspk.commit(m1*m2,r3)
        proof = nizk.multiplicationProof(self.ppatspk,a1,a2,a3,m1,m2,r1,r2,r3)
        m1p = randint(1,self.maxmessage)
        r1p = randint(1,self.n-1)
        d1,r1p = self.ppatspk.commit(m1p,r1p)
        m2p = randint(1,self.maxmessage)
        r2p = randint(1,self.n-1)
        d2,r2p = self.ppatspk.commit(m2p,r2p)
        g = self.ppatspp.g
        o1 = (r1p-r1)*g
        o2 = (r2p-r2)*g
        openings = (m1p-m1,o1),(m2p-m2,o2)

        d3 = nizk.multiplicationWithTripletAndCheck(self.ppatspk,d1,d2,a1,a2,a3,proof,openings)
        o3 = (r3+m2p*r1-m2*r1+m1p*r2-m1*r2)*g

        self.assertTrue(self.ppatspk.verifyOpening(d3,m1p*m2p,o3))

    def test_range_proof_on_commitment(self):
        m = randint(1,self.maxmessage)
        r = randint(1,self.n-1)
        com,r = self.ppatspk.commit(m,r)
        proof = nizk.base2RangeProof(self.ppatspk,com,m,r,self.maxexp,verif = True)
        self.assertTrue(nizk.base2RangeProofCheck(self.ppatspk,com,proof))

    def test_geq_proof_on_commitment(self):
        m1 = randint(1,self.maxmessage)
        m2 = randint(1,m1)
        com1, r1 = self.ppatspk.commit(m1)
        com2, r2 = self.ppatspk.commit(m2)
        gproof = nizk.geqProof(self.ppatspk,com1,m1,r1,com2,m2,r2,self.maxexp)
        res = nizk.geqProofCheck(self.ppatspk,com1,com2,gproof,self.maxexp)
        self.assertTrue(res)

    """
    def test_batch_verification(self):
        Com = []
        M = []
        O = []
        g = (self.ppatspp.g)
        l = 100
        for i in range(l):
            m = randint(1,self.n-1)
            r = randint(1,self.n-1)
            com,r = self.ppatspk.commit(m,r)
            o = r*g
            Com.append(com)
            M.append(m)
            O.append(o)

        self.assertTrue(self.ppatspk.verifyBatch(Com,M,O))
    """

    #TODO : test range proofs

suite = unittest.TestLoader().loadTestsFromTestCase(TestPPATS)
unittest.TextTestRunner(verbosity=2).run(suite)