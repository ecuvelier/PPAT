# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

import unittest
#import ppat.ppatc
from Crypto.Random.random import randint
from script import ppatcpp,ppatcpk,ppatcsk,n
import nizkproofs.nizkpok as nizk
import mathTools.otosEC as oEC

'''
x1c = randint(1,int(n-1));
x2c = randint(1,int(n-1));
g1c = x1c*Q
g2c = x2c*Q
h1tdc = randint(1,int(n-1));print "h1tdc trapdoor is", h1tdc
h1c = h1tdc*P
ppatcpp = ppat.ppatc.PPATCPublicParameters(P,Q,Pair,'Ate',psi=None,optim=True)
ppatcpk = ppat.ppatc.PPATCPublicKey(ppatcpp,g1c,g2c,h1c)
ppatcsk = ppat.ppatc.PPATCPrivateKey(ppatcpp, ppatcpk, x1c, x2c)
'''

class TestPPATC(unittest.TestCase):

    def setUp(self):
        self.n = int(n)
        self.ppatcpp = ppatcpp
        self.ppatcpk = ppatcpk
        self.ppatcsk = ppatcsk

    def test_encryption_decryption(self):
        m1 = randint(1,self.n-1)
        ECG = self.ppatcpp.g.ECG
        Jcoord = self.ppatcpp.Jcoord
        #m1 = m1i*P
        cipher1 = self.ppatcpk.encrypt(m1)
        mp1 = self.ppatcsk.decrypt(cipher1)
        mz1 = oEC.toEFp2(ECG,self.ppatcpk.encode(m1),Jcoord)
        self.assertEqual(mz1 , mp1)

    def test_encrypt_open_verify(self):
        m1 = randint(1,self.n-1)
        #m1 = m1i*P
        cipher1 = self.ppatcpk.encrypt(m1)
        a1 = self.ppatcsk.opens(cipher1)
        self.assertTrue(self.ppatcpk.verify(cipher1,m1,a1))


    def test_encrypt_with_consistency_check_proof(self):
        m1 = randint(1,self.n-1)
        #m1 = m1i*P
        c, cproof = self.ppatcpk.encryptwithCproof(m1)
        self.assertTrue(nizk.consistencyProofCheck_ppatc(self.ppatcpk,c,cproof))

    def test_commit_and_verify(self):
        m1 = randint(1,self.n-1)
        r1 = randint(1,self.n-1)
        r2 = randint(1,self.n-1)
        d = self.ppatcpk.commit(m1,r1,r2)
        self.assertTrue(self.ppatcpk.verifyCommitment(d,m1,r1,r2))

    def test_addition_of_ciphers(self):
        m1 = randint(1,self.n-1)
        #m1 = m1i*P
        cipher1 = self.ppatcpk.encrypt(m1)
        m2 = randint(1,self.n-1)
        #m2 = m2i*P
        cipher2 = self.ppatcpk.encrypt(m2)
        cipher3 = self.ppatcpk.encrypt(m1+m2)
        d1 = self.ppatcsk.decrypt(cipher1)
        d2 = self.ppatcsk.decrypt(cipher2)
        d3 = self.ppatcsk.decrypt(cipher3)
        self.assertTrue(d1+d2==d3)


    def test_multiplication_of_cipher_by_scalar(self):
        m1 = randint(1,self.n-1)
        #m1 = m1i*P
        cipher1 = self.ppatcpk.encrypt(m1)
        a = randint(1,1000)
        cipher2 = self.ppatcpk.encrypt((a*m1)%self.n)
        d1 = self.ppatcsk.decrypt(cipher1)
        d2 = self.ppatcsk.decrypt(cipher2)
        self.assertTrue(a*d1==d2)

    def test_addition_of_commitments(self):
        m1 = randint(1,self.n-1)
        r1 = randint(1,self.n-1)
        r2 = randint(1,self.n-1)
        d1 = self.ppatcpk.commit(m1,r1,r2)
        m1p = randint(1,self.n-1)
        r1p = randint(1,self.n-1)
        r2p = randint(1,self.n-1)
        d2 = self.ppatcpk.commit(m1p,r1p,r2p)
        d3 = d1+d2
        self.assertTrue(d3 == self.ppatcpk.commit(m1+m1p,r1+r1p,r2+r2p))

    def test_multiplication_of_commitment_by_a_scalar(self):
        m1 = randint(1,self.n-1)
        r1 = randint(1,self.n-1)
        r2 = randint(1,self.n-1)
        d1 = self.ppatcpk.commit(m1,r1,r2)
        a = randint(1,self.n-1)
        d2 = a*d1
        self.assertTrue(d2 == self.ppatcpk.commit((a*m1)%self.n,(a*r1)%self.n,(a*r2)%self.n))

    def test_multiplication_of_commitment_proof_and_check(self):
        m1 = randint(1,self.n-1)
        r11 = randint(1,self.n-1)
        r12 = randint(1,self.n-1)
        d1 = self.ppatcpk.commit(m1,r11,r12)
        m2 = randint(1,self.n-1)
        r21 = randint(1,self.n-1)
        r22 = randint(1,self.n-1)
        d2 = self.ppatcpk.commit(m2,r21,r22)
        r31 = randint(1,self.n-1)
        r32 = randint(1,self.n-1)
        d3 = self.ppatcpk.commit((m1*m2)%self.n,r31,r32)
        proof = nizk.multiplicationProof_ppatc(self.ppatcpk,d1,d2,d3,m1,m2,(r11,r12),(r21,r22),(r31,r32))
        self.assertTrue(nizk.multiplicationProofCheck_ppatc(self.ppatcpk,d1,d2,d3,proof))


suite = unittest.TestLoader().loadTestsFromTestCase(TestPPATC)
unittest.TextTestRunner(verbosity=2).run(suite)