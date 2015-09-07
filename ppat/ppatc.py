# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

################## AHO Commitment ############################
##############################################################
# These commitment schemes come from
# Abe, Haralambiev and Okhubo : Signing on elements in bilinear groups for modular protocol design, 2010.
# and
# Abe, Haralambiev and Okhubo :Group to group commitment do not shrink, 2012.
##############################################################


import gmpy, math
from Crypto.Random.random import randint
import mathTools.pairing as pairing
import mathTools.otosEC as oEC
import tools.utils as utils
import tools.fingexp as fingexp
import nizkproofs.nizkpok

class PPATCPublicParameters(fingexp.FingExp) :
    def __init__(self,P,Q,Pair,PUsed='Tate',psi=None, optim=False,Jcoord=False):

        assert isinstance(Pair,pairing.Pairing)

        self.Pair = Pair
        self.order = Pair.r # Order of the groups of the pairings
        self.optim = optim
        self.PUsed = PUsed
        self.Jcoord = Jcoord
        if self.PUsed == 'Tate' :
            # This pairing takes P in EFp and psi(Q) in EFp12
            if not self.optim :
                self.e = Pair.TatePairing
            else:
                self.e = oEC.OptimTatePairing
        elif self.PUsed == 'Ate' :
            if not self.optim :
                self.e = Pair.AtePairing
            else :
                self.e = oEC.OptimAtePairing
        assert not self.e==None

        self.g = Q # Generator of G1
        self.h = P # Generator of G2' homomorphic to G2
        if self.Jcoord :
            self.g.toJcoord()
            self.h.toJcoord()
        if psi == None:
            def psi(a):
                return a
        self.psi = psi
        # either psi: G2'---> G2 ; Pairing.Q = psi(h) is generator of G2
        # either psi is identity
        #assert self.psi(self.h) == self.Pairing.Q

        self.to_fingerprint = ["Pair","order","optim","PUsed","g","h"]
        self.to_export = {"fingerprint": [],"value": ["Pair","order","optim","Pused","g","h"]}

    def __eq__(self, other):
       return (self.g == other.g and self.h == other.h and self.Pair == other.Pair and self.psi == other.psi)

    def __str__(self):
        return "PPATCPublicParameters :\n "+str(self.Pair)

class PPATCPublicKey(fingexp.FingExp) :
    def __init__(self,PPATCpp,g1,g2,h1):
        self.PPATCpp = PPATCpp
        self.g1 = g1 # in G1
        self.g2 = g2 # in G1
        self.h1 = h1 # in G2'
        #psi = self.PPATCpp.psi
        #self.hashf = None # Hash function to be implemented

        #assert g1.ECG == self.PPATCpp.Pair.ECG
        #assert g2.ECG == self.PPATCpp.Pair.ECG
        Jcoord = self.PPATCpp.Jcoord
        if Jcoord :
            self.g1.toJcoord()
            self.g2.toJcoord()
            self.h1.toJcoord()
        #assert psi(h1).ECG == self.PPATCpp.Pairing.EFqp

        w = 10
        m = len(utils.binn(self.PPATCpp.order))
        #m = 160
        d = int(math.ceil(float(m)/w))
        e = int(math.ceil(float(d)/2))

        # Precomputed tables to fasten the scalr multiplication with the generators
        self.precomp_g = oEC.prec_comb2_EFp2(w,m,self.PPATCpp.g,Jcoord),w,m,d,e
        self.precomp_h = oEC.prec_comb2_EFp(w,m,self.PPATCpp.h,Jcoord),w,m,d,e
        self.precomp_g1 = oEC.prec_comb2_EFp2(w,m,self.g1,Jcoord),w,m,d,e
        self.precomp_g2 = oEC.prec_comb2_EFp2(w,m,self.g2,Jcoord),w,m,d,e
        self.precomp_h1 = oEC.prec_comb2_EFp(w,m,self.h1,Jcoord),w,m,d,e


        self.to_fingerprint = ["PPATCpp","g1","g2","h1"]
        self.to_export = {"fingerprint": [],"value": ["PPATCpp","g1","g2","h1"]}

    def __eq__(self, other):
       return (self.PPATCpp == other.PPATCpp and self.g1 == other.g1 and self.g2 == other.g2 and self.h1 == other.h1)

    def hashf(self,L):
        ''' Return a number in Zq computed from a list L of elements
            Assuming that all elements of the list has a fingerprint
        '''
        q = self.PPATCpp.order
        f = fingexp.fingerprint(L)
        r = utils.b64tompz(f)%q
        return r

    def encode(self,m):
        ''' Return a torsion point over EFp which is m*g (or m*P)
        '''
        Jcoord = self.PPATCpp.Jcoord
        ECG = self.g1.ECG
        mt = oEC.mul_comb2_EFp2(ECG,m,self.precomp_g,Jcoord)
        return mt

    def encrypt(self,m,r1=None,r2=None, r3=None):
        ''' Outputs a PPATCCiphertext on m using r1,r2 as the randomness for the
        commitment and r1,r2,r3 as the randomness for the encryption
        '''

        # notations
        q = self.PPATCpp.order
        g = self.PPATCpp.g
        ECG = g.ECG # EFp2
        Jcoord = self.PPATCpp.Jcoord

        if r1 == None:
            r1 = randint(1,int(q))
        if r2 == None:
            r2 = randint(1,int(q))
        if r3 == None:
            r3 = randint(1,int(q))

        # commitment
        d = self.commit(m,r1,r2)

        # encryption
        c1t = oEC.mul_comb2_EFp2(ECG,r2,self.precomp_g,Jcoord)
        c1 = oEC.toEFp2(ECG,c1t,Jcoord)
        #c1 = r2*g
        c2t = oEC.mul_comb2_EFp2(ECG,r3,self.precomp_g,Jcoord)
        c2 = oEC.toEFp2(ECG,c2t,Jcoord)
        #c2 = r3*g
        c31t = oEC.mul_comb2_EFp2(ECG,r1,self.precomp_g1,Jcoord)
        c32t = oEC.mul_comb2_EFp2(ECG,r3,self.precomp_g2,Jcoord)
        c3t = oEC.addEFp2(ECG,c31t,c32t,Jcoord)
        c3 = oEC.toEFp2(ECG,c3t,Jcoord)
        #c3 = (r1*g1)+(r3*g2)

        return PPATCCiphertext(d,c1,c2,c3,self)

    def commit(self,m,r1=None,r2=None):

        q = self.PPATCpp.order
        if r1 == None:
            r1 = randint(1,int(q))
        if r2 == None:
            r2 = randint(1,int(q))

        # notations
        Jcoord = self.PPATCpp.Jcoord
        ECG1 = self.h1.ECG
        ECG2 = self.g1.ECG

        # commitment
        d11t = oEC.mul_comb2_EFp(ECG1,r1,self.precomp_h,Jcoord)
        d12t = oEC.mul_comb2_EFp(ECG1,r2,self.precomp_h1,Jcoord)
        d1t = oEC.addEFp(ECG1,d11t,d12t,Jcoord)
        d1 = oEC.toEFp(ECG1,d1t,Jcoord)
        #d1 = (r1*h)+(r2*h1)
        mp = self.encode(m)
        d21t = oEC.mul_comb2_EFp2(ECG2,r2,self.precomp_g1,Jcoord)
        d2t = oEC.addEFp2(ECG2,mp,d21t,Jcoord)
        d2 = oEC.toEFp2(ECG2,d2t,Jcoord)
        #d2 = mp + r2*g1

        return PPATCCommitment(d1,d2,self)


    def derivCom(self,c):
        assert isinstance(c,PPATCCiphertext)
        return c.d

    def verify(self,c,m,a):

        assert isinstance(c,PPATCCiphertext)

        mp = oEC.toEFp2(self.g1.ECG,self.encode(m),self.PPATCpp.Jcoord)

        # notoations
        Pair = self.PPATCpp.Pair
        d = self.derivCom(c)
        d1,d2 = d.d1,d.d2
        g1 = self.g1
        h = self.PPATCpp.h
        h1 = self.h1
        e = self.PPATCpp.e
        psi = self.PPATCpp.psi
        psih = psi(h)
        psih1 = psi(h1)
        psid1 = psi(d1)

        return e(psid1,g1,Pair) == e(psih,a,Pair)*e(psih1,d2-mp,Pair)

    def verifyCommitment(self,com,m,r1,r2):

        assert isinstance(com,PPATCCommitment)
        d = self.commit(m,r1,r2)
        return d == com

    def encryptwithCproof(self,m,r1=None,r2=None,r3=None,s=None,s1=None,s2=None,s3=None):
        q = self.PPATCpp.order

        if r1 == None:
            r1 = randint(1,int(q))
        if r2 == None:
            r2 = randint(1,int(q))
        if r3 == None:
            r3 = randint(1,int(q))
        c = self.encrypt(m,r1,r2,r3)
        cproof = nizkproofs.nizkpok.consistencyProof_ppatc(self,c,m,r1,r2,r3,s,s1,s2,s3)
        return c,cproof

    def __str__(self):
        return "PPATCPublicKey :\n"+str(self.PPATCpp)+"\n g1 :\n"+str(self.g1)+"\n g2 :\n"+str(self.g2)+"\n h1 :\n"+str(self.h1)

class PPATCPrivateKey :
    def __init__(self,PPATCpp, PPATCpk, x1, x2):
        self.PPATCpp = PPATCpp
        self.PPATCpk = PPATCpk
        assert self.PPATCpp ==  self.PPATCpk.PPATCpp
        self.x1 = x1
        self.x2 = x2 # the private keys
        g = self.PPATCpp.g
        g1 = self.PPATCpk.g1
        g2 = self.PPATCpk.g2
        assert g1 == g*self.x1
        assert g2 == g*self.x2

    def __eq__(self, other):
       return (self.x1 == other.x1 and self.x2 == other.x2 and self.PPATCpp == other.PPATCpp and self.PPATCpk == other.PPATCpk)

    def decrypt(self,c):

        assert isinstance(c,PPATCCiphertext)

        #notations
        Jcoord = self.PPATCpp.Jcoord
        ECG = self.PPATCpp.g.ECG
        d2 = c.d.d2
        d2t = oEC.toTupleEFp2(d2,Jcoord)
        c1 = c.c1
        c1t = oEC.toTupleEFp2(c1,Jcoord)
        c1x1t = oEC.mulECP(ECG,c1t,-self.x1,sq= True, Jcoord = Jcoord)
        d2c1x1t = oEC.addEFp2(ECG,d2t,c1x1t,Jcoord)
        dec = oEC.toEFp2(ECG,d2c1x1t,Jcoord)
        # dec = d2 - (self.x1*c1)

        return dec

    def opens(self,c):

        assert isinstance(c,PPATCCiphertext)

        #notations
        Jcoord = self.PPATCpp.Jcoord
        ECG = self.PPATCpp.g.ECG
        c2 = c.c2
        c3 = c.c3
        c2t = oEC.toTupleEFp2(c2,Jcoord)
        c3t = oEC.toTupleEFp2(c3,Jcoord)
        c2x2t = oEC.mulECP(ECG,c2t,-self.x2,sq= True, Jcoord = Jcoord)
        c3c2x2t = oEC.addEFp2(ECG,c3t,c2x2t,Jcoord)
        ope = oEC.toEFp2(ECG,c3c2x2t,Jcoord)
        # ope = c3-(self.x2*c2)

        return ope

    def __str__(self):
        return "PPATCPrivateKey :\n"+str(self.PPATCpp)+"\n "+str(self.PPATCpk)+"\n x1 :\n"+str(self.x1)+"\n x2 :\n"+str(self.x2)

class PPATCCiphertext(fingexp.FingExp) :
    def __init__(self,d,c1,c2,c3,PPATCpk):
        self.d = d
        self.c1 = c1
        self.c2 = c2
        self.c3 = c3
        self.PPATCpk = PPATCpk

        self.to_fingerprint = ["PPATCpk","d","c1","c2","c3"]
        self.to_export = {"fingerprint": [],"value": ["PPATCpk","d","c1","c2","c3"]}

    def __eq__(self,other):
        return (self.d == other.d and self.c1 == other.c1 and self.c2 == other.c2 and self.c3 == other.c3 and self.PPATCpk == other.PPATCpk)

    def __str__(self):
        return "PPATCCiphertext :\n d :\n"+str(self.d)+"\n c1 :\n"+str(self.c1)+"\n c2 :\n"+str(self.c2)+"\n c3 :\n"+str(self.c3)

    def __add__(self,b):
        ''' Addition between two PPATC ciphertext
            The result is a PPATC ciphertext which encrypts and commits
            on the sum of the initial messages
        '''
        assert isinstance(b,PPATCCiphertext)
        assert self.PPATCpk == b.PPATCpk # ciphertexts built using the same public key
        Jcoord = self.PPATCpk.PPATCpp.Jcoord
        ECG = self.PPATCpk.g1.ECG

        newcom = self.d+b.d
        c1t = oEC.toTupleEFp2(self.c1,Jcoord)
        bc1t = oEC.toTupleEFp2(b.c1,Jcoord)
        nc1t = oEC.addEFp2(ECG,c1t,bc1t,Jcoord)
        newc1 = oEC.toEFp2(ECG,nc1t,Jcoord)
        c2t = oEC.toTupleEFp2(self.c2,Jcoord)
        bc2t = oEC.toTupleEFp2(b.c2,Jcoord)
        nc2t = oEC.addEFp2(ECG,c2t,bc2t,Jcoord)
        newc2 = oEC.toEFp2(ECG,nc2t,Jcoord)
        c3t = oEC.toTupleEFp2(self.c3,Jcoord)
        bc3t = oEC.toTupleEFp2(b.c3,Jcoord)
        nc3t = oEC.addEFp2(ECG,c3t,bc3t,Jcoord)
        newc3 = oEC.toEFp2(ECG,nc3t,Jcoord)
        return PPATCCiphertext(newcom,newc1,newc2,newc3,self.PPATCpk)

    def __sub__(self,a):
        return self.__add__(-a)

    def __neg__(self):
        return PPATCCiphertext(-self.d,-self.c1,-self.c2,-self.c3, self.PPATCpk)

    def __mul__(self,a):
        '''multiplication by a scalar
           The result is a PPATC Ciphertext which encrypts and commits on e*m
        '''
        m = gmpy.mpz(1)
        if not isinstance(a, int) and not isinstance(a, long) and not type(a)==type(m):
            raise Exception("Multiplication of a PPATC Ciphertext by a non integer, long or mpz")
        else :
            Jcoord = self.PPATCpk.PPATCpp.Jcoord
            ECG = self.PPATCpk.g1.ECG
            c1t = oEC.toTupleEFp2(self.c1,Jcoord)
            nc1t = oEC.mulECP(ECG,c1t,a,sq=True,Jcoord=Jcoord)
            newc1 = oEC.toEFp2(ECG,nc1t,Jcoord)
            c2t = oEC.toTupleEFp2(self.c2,Jcoord)
            nc2t = oEC.mulECP(ECG,c2t,a,sq=True,Jcoord=Jcoord)
            newc2 = oEC.toEFp2(ECG,nc2t,Jcoord)
            c3t = oEC.toTupleEFp2(self.c3,Jcoord)
            nc3t = oEC.mulECP(ECG,c3t,a,sq=True,Jcoord=Jcoord)
            newc3 = oEC.toEFp2(ECG,nc3t,Jcoord)
            return PPATCCiphertext(a*self.d,newc1,newc2,newc3,self.PPATCpk)

    def __rmul__(self, other):
        return self.__mul__(other)

class PPATCCommitment(fingexp.FingExp):
    def __init__(self,d1,d2,PPATCpk):
        self.d1 = d1
        self.d2 = d2
        self.PPATCpk = PPATCpk

        self.to_fingerprint = ["PPATCpk","d1", "d2"]
        self.to_export = {"fingerprint": [],"value": ["PPATCpk","d1","d2"]}

    def __eq__(self,other):
        return (self.d1 == other.d1 and self.d2 == other.d2 and self.PPATCpk == other.PPATCpk)

    def __str__(self):
        return "PPATCCommitment :\n d1 :\n"+str(self.d1)+" d2 :\n"+str(self.d2)

    def __add__(self,b):
        ''' Addition between two PPATC commitments
            The result is a PPATC commitment which commits
            on the sum of the initial messages
        '''
        assert isinstance(b,PPATCCommitment)
        assert self.PPATCpk == b.PPATCpk # commitments built using the same public key
        Jcoord = self.PPATCpk.PPATCpp.Jcoord
        ECG1 = self.PPATCpk.h1.ECG
        ECG2 = self.PPATCpk.g1.ECG

        d1t = oEC.toTupleEFp(self.d1,Jcoord)
        bd1t = oEC.toTupleEFp(b.d1,Jcoord)
        nd1t = oEC.addEFp(ECG1,d1t,bd1t,Jcoord)
        newd1 = oEC.toEFp(ECG1,nd1t,Jcoord)
        d2t = oEC.toTupleEFp2(self.d2,Jcoord)
        bd2t = oEC.toTupleEFp2(b.d2,Jcoord)
        nd2t = oEC.addEFp2(ECG2,d2t,bd2t,Jcoord)
        newd2 = oEC.toEFp2(ECG2,nd2t,Jcoord)
        return PPATCCommitment(newd1,newd2,self.PPATCpk)

    def __sub__(self,a):
        assert isinstance(a,PPATCCommitment)
        return self.__add__(-a)

    def __neg__(self):
        return PPATCCommitment(-self.d1,-self.d2,self.PPATCpk)

    def __mul__(self,a):
        '''multiplication by a scalar a
           The result is a PPATC Commitment which encrypts and commits on a*m
        '''
        m = gmpy.mpz(1)
        if not isinstance(a, int) and not isinstance(a, long) and not type(a)==type(m):
            raise Exception("Multiplication of a PPATC Commitment by a non integer, long or mpz")
        else :
            Jcoord = self.PPATCpk.PPATCpp.Jcoord
            ECG1 = self.PPATCpk.h1.ECG
            ECG2 = self.PPATCpk.g1.ECG
            d1t = oEC.toTupleEFp(self.d1,Jcoord)
            nd1t = oEC.mulECP(ECG1,d1t,a,sq=False,Jcoord=Jcoord)
            newd1 = oEC.toEFp(ECG1,nd1t,Jcoord)
            d2t = oEC.toTupleEFp2(self.d2,Jcoord)
            nd2t = oEC.mulECP(ECG2,d2t,a,sq=True,Jcoord=Jcoord)
            newd2 = oEC.toEFp2(ECG2,nd2t,Jcoord)
            return PPATCCommitment(newd1,newd2,self.PPATCpk)

    def __rmul__(self, other):
        return self.__mul__(other)
