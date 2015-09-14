# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

from Crypto.Random.random import randint
import ppat.ppats
import ppat.ppatc
import mathTools.otosEC as oEC


###################################################################################
######################### Consistency Proof #######################################
###################################################################################

def consitencyProof(ppatspk,c,m,r,s,mp=None,rp=None,sp=None):
    ''' Return a NIZK proof that a PPATSciphertext c contains
    a commitment consistent with an encyrption
    respectievely to a message m and some opening value (r,s)
    mp,rp,sp are the randomness used in the proof (optional)
    '''
    #assert isinstance(c,ppats.PPATSCiphertext)
    order = ppatspk.PPATSpp.order
    if mp == None:
        mp = randint(1,int(order))
    if rp == None:
        rp = randint(1,int(order))
    if sp == None:
        sp = randint(1,int(order))

    cp = ppatspk.encrypt(mp,rp,sp)
    # challenge
    nu = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,c,cp])
    # response
    zm = (mp+nu*m)%order
    zr = (rp+nu*r)%order
    zs = (sp+nu*s)%order

    return [nu,zm,zr,zs]

def consistencyProof_ppatc(ppatcpk,c,m,r1,r2,r3,s=None,s1=None,s2=None,s3=None):
    ''' This proof ensures that the commitment part of the ciphertext is
    commiting on the same message that is encrypted in the encryption part
    The proof is a proof of equality between discrete logarithms
    '''

    # notations
    '''
    h = ppatcpk.PPATCpp.h
    ECG1 = h.ECG
    h1 = ppatcpk.h1
    g = ppatcpk.PPATCpp.g
    ECG2 = g.ECG
    Jcoord = ppatcpk.PPATCpp.Jcoord
    g1 = ppatcpk.g1
    g2 = ppatcpk.g2
    '''
    q = ppatcpk.PPATCpp.order

    if s1 == None:
        s1 = randint(1,int(q))
    if s2 == None:
        s2 = randint(1,int(q))
    if s3 == None:
        s3 = randint(1,int(q))
    if s == None:
        s = randint(1,int(q))
    '''
    ms = ppatcpk.encode(s) # ms is a random element of G1

    c1pt = oEC.mul_comb2_EFp2(ECG2,s2,ppatcpk.precomp_g,Jcoord)
    c1p = oEC.toEFp2(ECG2,c1pt,Jcoord)
    c1p = s2*g
    c2p = s3*g
    c3p = s1*g1 + s3*g2
    d1p = s1*h + s2*h1
    d2p = ms + s2*g1
    dp = ppat.ppatc.PPATCCommitment(d1p,d2p,ppatcpk)
    cp = ppat.ppatc.PPATCCiphertext(dp,c1p,c2p,c3p,ppatcpk)
    '''
    cp = ppatcpk.encrypt(s,s1,s2,s3)

    nu = ppatcpk.hashf([ppatcpk.PPATCpp,ppatcpk,c,cp])

    f1 = (s1 + nu*r1)%q
    f2 = (s2 + nu*r2)%q
    f3 = (s3 + nu*r3)%q
    #fm = (mp + nu*m) %q
    fm = (s + nu*m) %q

    return [nu,f1,f2,f3,fm]

def consistencyProofCheck(ppatspk,c,proof):
    ''' Checks the validity of the proof in regards to c
    '''
    #assert isinstance(c,ppats.PPATSCiphertext)
    nu,zm,zr,zs = proof
    cz = ppatspk.encrypt(zm,zr,zs)
    cp = cz-(c*nu)

    nup = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,c,cp])
    return nup == nu

def consistencyProofCheck_ppatc(ppatcpk,c,proof):

    nu,f1,f2,f3,fm = proof
    #assert isinstance(c,PPATCCiphertext)

    # notations
    '''
    h = ppatcpk.PPATCpp.h
    h1 = ppatcpk.h1
    g = ppatcpk.PPATCpp.g
    g1 = ppatcpk.g1
    g2 = ppatcpk.g2
    c1 = c.c1
    c2 = c.c2
    c3 = c.c3
    d = ppatcpk.derivCom(c)
    d1 = d.d1
    d2 = d.d2
    fmp = ppatcpk.encode(fm) # fmp is a point of G1
    c1p = g*f2 - nu*c1
    c2p = g*f3 - nu*c2
    c3p = g1*f1 + g2*f3 - nu*c3
    d1p = h*f1 + h1*f2 - nu*d1
    d2p = fmp + g1*f2 - nu*d2
    dp = ppat.ppatc.PPATCCommitment(d1p,d2p,ppatcpk)
    cp = ppat.ppatc.PPATCCiphertext(dp,c1p,c2p,c3p,ppatcpk)
    '''
    cf = ppatcpk.encrypt(fm,f1,f2,f3)
    cp = cf - (c*nu)

    nup = ppatcpk.hashf([ppatcpk.PPATCpp,ppatcpk,c,cp])
    return nu == nup

###################################################################################
######################### Verifiability Proof #####################################
###################################################################################

def verifiabilityProof(ppatspk,d,m,r,s=None,u=None,t=None):
    ''' This ZK proof ensures that d = r*h+m*h1 is a commitment on m = 0 or 1
    b,u,t are the randomness used in the proof (optional)
    '''
    # notations
    order = ppatspk.PPATSpp.order

    assert m==0 or m==1 # the proof works only if m = 0 or 1

    if s == None:
        s = randint(1,int(order))
    if u == None:
        u = randint(1,int(order))
    if t == None:
        t = randint(1,int(order))

    if m == 0 :
        #commitment
        u1 = u
        t1 = t
        w0,s = ppatspk.commit(0,s)
        w1,r1 = ppatspk.commit(t1,u1-t1*r)
        # challenge
        t0 = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d,w0,w1])-t1
        # response
        u0 = (s+r*t0)%order
    else :
        # m == 1
        #commitment
        u0 = u
        t0 = t
        w0,r0 = ppatspk.commit(-t0,u0-t0*r)
        w1,s = ppatspk.commit(0,s)
        # challenge
        t1 = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d,w0,w1])-t0
        # response
        u1 = (s+r*t1)%order
    return [u0,u1,t0,t1]

def verifiabilityProofCheck(ppatspk,d,proof):
    ''' Return True if the ZKP proof is correct with respect to d
    meaning that d is a commitment on either 0 or 1
    '''
    u0,u1,t0,t1 = proof
    # notations
    Jcoord = ppatspk.PPATSpp.Jcoord
    ECG = ppatspk.PPATSpp.h.ECG

    ddt = oEC.toTupleEFp(d.d,Jcoord)

    u0ht = oEC.mul_comb2_EFp(ECG,u0,ppatspk.precomp_h,Jcoord)
    ddt0 = oEC.mulECP(ECG,ddt,-t0,False,Jcoord)
    w0t = oEC.addEFp(ECG,u0ht,ddt0,Jcoord)
    w0v = oEC.toEFp(ECG,w0t,Jcoord)
    w0 = ppat.ppats.PPATSCommitment(w0v,ppatspk)

    ddt1 = oEC.mulECP(ECG,ddt,-t1,False,Jcoord)
    u1ht = oEC.mul_comb2_EFp(ECG,u1,ppatspk.precomp_h,Jcoord)
    t1h1t = oEC.mul_comb2_EFp(ECG,t1,ppatspk.precomp_h1,Jcoord)
    ad1 = oEC.addEFp(ECG,ddt1,u1ht,Jcoord)
    w1t = oEC.addEFp(ECG,ad1,t1h1t,Jcoord)
    w1v = oEC.toEFp(ECG,w1t,Jcoord)
    w1 = ppat.ppats.PPATSCommitment(w1v,ppatspk)

    return t0+t1 == ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d,w0,w1])

def verifiabilityProof2(ppatspk,d,m,r,b=None,u=None,t=None):
    ''' This ZK proof ensures that d = r*h+m*h1 is a commitment on m = 0 or 1
    b,u,t are the randomness used in the proof (optional)
    '''
    # notations
    order = ppatspk.PPATSpp.order
    h = ppatspk.PPATSpp.h
    h1 = ppatspk.h1
    ECG = h.ECG
    Jcoord = ppatspk.PPATSpp.Jcoord
    #ht = oEC.toTupleEFp(ECG,h,Jcoord)
    nh1t = oEC.toTupleEFp(ECG,-h1,Jcoord)
    ddt = oEC.toTupleEFp(ECG,d.d,Jcoord)
    #assert h*r+h1*m == d.d # commitment is well formed
    assert m==0 or m==1 # the proof works only if m = 0 or 1

    if b == None:
        b = randint(1,int(order))
    if u == None:
        u = randint(1,int(order))
    if t == None:
        t = randint(1,int(order))

    hbt = oEC.mul_comb2_EFp(ECG,b,ppatspk.precomp_h,Jcoord)
    hb = oEC.toEFp(ECG,hbt,Jcoord)
    if m == 0:
        u1 = u
        t1 = t
        # commitment

        #w0 = PPATSCommitment(h*b,self)
        w0 = ppat.ppats.PPATSCommitment(hb,ppatspk)
        hu1t = oEC.mul_comb2_EFp(ECG,u1,ppatspk.precomp_h,Jcoord)
        s1 = oEC.addEFp(ECG,ddt,nh1t,Jcoord)
        s1t1 = oEC.mulECP(ECG,s1,-t1,False,Jcoord)
        w1t = oEC.addEFp(ECG,hu1t,s1t1,Jcoord)
        w1v = oEC.toEFp(ECG,w1t,Jcoord)
        w1 = ppat.ppats.PPATSCommitment(w1v,ppatspk)
        # challenge
        t0 = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d,w0,w1])-t1
        # response
        u0 = b+r*t0
    if m == 1:
        u0 = u
        t0 = t
        # commitment
        hu0t = oEC.mul_comb2_EFp(ECG,u0,ppatspk.precomp_h,Jcoord)
        ddt0 = oEC.mulECP(ECG,ddt,-t0,False,Jcoord)
        w0t = oEC.addEFp(ECG,hu0t,ddt0,Jcoord)
        w0v = oEC.toEFp(ECG,w0t,Jcoord)
        w0 = ppat.ppats.PPATSCommitment(w0v,ppatspk)
        w1 = ppat.ppats.PPATSCommitment(hb,ppatspk)
        # challenge
        t1 = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d,w0,w1])-t0
        # response
        u1 = b+r*t1
    return [u0,u1,t0,t1]

    """
    def verifiabilityProofCheck2(self,d,proof):
        ''' Return True if the ZKP proof is correct with respect to d
            meaning that d is a commitment on either 0 or 1
        '''
        u0,u1,t0,t1 = proof
        # notations
        h = self.PPATSpp.h
        h1 = self.h1
        EFq = h.EFq
        ht = h.toTupleEFp()
        nh1t = (-h1).toTupleEFp()
        ddt = d.d.toTupleEFp()

        hu0t = EFq.mulFp(ht,u0)
        ddt0 = EFq.mulFp(ddt,-t0)
        w0t = EFq.taddFp(hu0t,ddt0)
        w0v = EFq.toEFp(w0t)

        w0 = PPATSCommitment(w0v,self)
        #w0 = PPATSCommitment(h*u0-d.d*t0,self)
        hu1t = EFq.mulFp(ht,u1)
        ddth1 = EFq.taddFp(ddt,nh1t)
        s1t = EFq.mulFp(ddth1,-t1)
        w1t = EFq.taddFp(hu1t,s1t)
        w1v = EFq.toEFp(w1t)
        w1 = PPATSCommitment(w1v,self)
        #w1 = PPATSCommitment(h*u1-(d.d-h1)*t1,self)

        return t0+t1 == self.hashf([self.PPATSpp,self,d,w0,w1])
    """

###################################################################################
######################### Multiplication Proof ####################################
###################################################################################

def multiplicationProof(ppatspk, d1,d2,d3,m1,m2,r1,r2,r3, m1p=None, m2p=None, r1p=None, r2p=None, r3p=None, check= False):
    ''' Assuming d1, d2 are commitments on m1, m2 with randomness r1, r2
    respectively. Assuming r3 is the randomness used in d3.
    The output of the method is a NIZK PoK that d3 is a commitment
    on the product m1*m2.
    m1p, m2p, r1p, r2p, r3p are the values used in the proof. They are chosen
    randomly if not provided.
    check is a boolean : if set True then, the methods runs verifications on
    d1,d2,d3
    '''
    if check :
        assert isinstance(d1,ppat.ppats.PPATSCommitment)
        assert isinstance(d2,ppat.ppats.PPATSCommitment)
        assert isinstance(d3,ppat.ppats.PPATSCommitment)
        assert d1,r1 == ppatspk.commit(m1,r1)
        assert d2,r2 == ppatspk.commit(m2,r2)
        assert d3,r3 == ppatspk.commit(m1*m2,r3)

    order = ppatspk.PPATSpp.order
    if m1p == None:
        m1p = randint(1,int(order))
    if m2p == None:
        m2p = randint(1,int(order))
    if r1p == None:
        r1p = randint(1,int(order))
    if r2p == None:
        r2p = randint(1,int(order))
    if r3p == None:
        r3p = randint(1,int(order))

    d1p,r1p = ppatspk.commit(m1p,r1p)
    d2p,r2p = ppatspk.commit(m2p,r2p)
    d3p,r3pb = ppatspk.commit(m1*m2p,r3p+m2p*r1)

    nu = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d1,d2,d3,d1p,d2p,d3p])

    z1 = (m1p+nu*m1)%order
    z2 = (m2p+nu*m2)%order
    s1 = (r1p+nu*r1)%order
    s2 = (r2p+nu*r2)%order
    s3 = (r3p+nu*(r3-m2*r1))%order

    return [nu,z1,z2,s1,s2,s3]

def multiplicationProof_ppatc(ppatcpk,d1,d2,d3,m1,m2,r1,r2,r3,m1p=None,m2p=None,m5p=None, r1p=None,r2p=None,r3p=None,r4p=None,r5p=None,check = False):
    ''' This method returns a NIZK proof that the commitment d3 commits on m3,
        the product of the values commited in d1 and d2 (m1 and m2) : m3 = m1*m2.
        r1,r2,r3 are the randomness used in the commitments d1,d2,d3.
        m1p,m2p,r1p,r2p,r3p are the randomness used in the proof.
        The proof theoretic details such as soundness is provided in #TODO
    '''
    r11, r12 = r1
    r21, r22 = r2
    r31, r32 = r3
    q = ppatcpk.PPATCpp.order
    if check :
        assert isinstance(d1,ppat.ppatc.PPATCCommitment)
        assert isinstance(d2,ppat.ppatc.PPATCCommitment)
        assert isinstance(d3,ppat.ppatc.PPATCCommitment)
        assert d1 == ppatcpk.commit(m1,r11,r12)
        assert d2 == ppatcpk.commit(m2,r21,r22)
        assert d3 == ppatcpk.commit((m1*m2)%q,r31,r32)

    # Randomness assignations
    if m1p == None :
        m1p =  randint(1,int(q))
    if m2p == None :
        m2p =  randint(1,int(q))
    if m5p == None :
        m5p =  randint(1,int(q))
    if r1p == None :
        r1p1 = randint(1,int(q))
        r1p2 = randint(1,int(q))
    else :
        r1p1,r1p2 = r1p
        assert(not r1p1 == None and not r1p2 == None)
    if r2p == None :
        r2p1 = randint(1,int(q))
        r2p2 = randint(1,int(q))
    else :
        r2p1,r2p2 = r2p
        assert(not r2p1 == None and not r2p2 == None)
    if r3p == None :
        r3p1 = randint(1,int(q))
        r3p2 = randint(1,int(q))
    else :
        r3p1,r3p2 = r3p
        assert(not r3p1 == None and not r3p2 == None)
    if r4p == None :
        r4p1 = randint(1,int(q))
        r4p2 = randint(1,int(q))
    else :
        r4p1,r4p2 = r4p
        assert(not r4p1 == None or not r4p2 == None)
    if r5p == None :
        r5p1 = randint(1,int(q))
        r5p2 = randint(1,int(q))
    else :
        r5p1,r5p2 = r5p
        assert(not r5p1 == None or not r5p2 == None)

    d1p = ppatcpk.commit(m1p,r1p1,r1p2)
    d2p = ppatcpk.commit(m2p,r2p1,r2p2)
    d3p = ppatcpk.commit((m1p*m2p)%q,r3p1,r3p2)
    d4 = ppatcpk.commit((m1*m2p+m1p*m2)%q,r4p1,r4p2)
    #d4 is a new commitment on wich a knowledge of opening has to be proven
    d5p = ppatcpk.commit(m5p,r5p1,r5p2)

    # challenge
    nu = ppatcpk.hashf([d1,d2,d3,d4,d1p,d2p,d3p,d5p,ppatcpk])

    # responses
    z1 = (m1p+nu*m1)%q
    z2 = (m2p+nu*m2)%q
    z5 = (m5p+nu*(m1*m2p+m1p*m2))%q
    s11 = (r1p1+nu*r11)%q
    s12 = (r1p2+nu*r12)%q
    s21 = (r2p1+nu*r21)%q
    s22 = (r2p2+nu*r22)%q

    s31 = (r3p1+nu*r4p1+(nu**2)*r31)%q
    s32 = (r3p2+nu*r4p2+(nu**2)*r32)%q
    s51 = (r5p1+nu*r4p1)%q
    s52 = (r5p2+nu*r4p2)%q

    return d4,nu,z1,z2,z5,s11,s12,s21,s22,s31,s32,s51,s52

def multiplicationProofCheck(ppatspk,d1,d2,d3,proof):
    ''' d1,d2,d3 are PPATS Commitment
    proof is a ZK proof that d3 commits on the
    product of the message commited in d1 and d2.
    the method returns True if this assertion is correct and False
    otherwise
    '''
    #assert isinstance(d1,ppat.ppats.PPATSCommitment)
    #assert isinstance(d2,ppat.ppats.PPATSCommitment)
    #assert isinstance(d3,ppat.ppats.PPATSCommitment)
    # Notations
    ECG = ppatspk.PPATSpp.h.ECG
    Jcoord = ppatspk.PPATSpp.Jcoord

    nu,z1,z2,s1,s2,s3 = proof

    #a1 = s1*h + z1*h1
    a1c,s1 = ppatspk.commit(z1,s1)
    a1 = a1c.d
    #a2 = s2*h + z2*h1
    a2c,s2 = ppatspk.commit(z2,s2)
    a2 = a2c.d
    s3ht = oEC.mul_comb2_EFp(ECG,s3,ppatspk.precomp_h,Jcoord)
    d1t = oEC.toTupleEFp(d1.d,Jcoord)
    z2d1t = oEC.mulECP(ECG,d1t,z2,False,Jcoord)
    a3t = oEC.addEFp(ECG,s3ht,z2d1t,Jcoord)
    #a3 = s3*h + z2*d1.d
    d2t = oEC.toTupleEFp(d2.d,Jcoord)
    d3t = oEC.toTupleEFp(d3.d,Jcoord)
    mnud1t = oEC.mulECP(ECG,d1t,-nu,False,Jcoord)
    mnud2t = oEC.mulECP(ECG,d2t,-nu,False,Jcoord)
    mnud3t = oEC.mulECP(ECG,d3t,-nu,False,Jcoord)
    a1t = oEC.toTupleEFp(a1,Jcoord)
    a2t = oEC.toTupleEFp(a2,Jcoord)

    e1t = oEC.addEFp(ECG,a1t,mnud1t,Jcoord)
    e2t = oEC.addEFp(ECG,a2t,mnud2t,Jcoord)
    e3t = oEC.addEFp(ECG,a3t,mnud3t,Jcoord)
    e1 = oEC.toEFp(ECG,e1t,Jcoord)
    e2 = oEC.toEFp(ECG,e2t,Jcoord)
    e3 = oEC.toEFp(ECG,e3t,Jcoord)

    d1p = ppat.ppats.PPATSCommitment(e1,ppatspk)
    d2p = ppat.ppats.PPATSCommitment(e2,ppatspk)
    d3p = ppat.ppats.PPATSCommitment(e3,ppatspk)

    nup = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,d1,d2,d3,d1p,d2p,d3p])

    return nu == nup

def multiplicationProofCheck_ppatc(ppatcpk,d1,d2,d3,proof):
    #assert isinstance(d1,PPATCCommitment)
    #assert isinstance(d2,PPATCCommitment)
    #assert isinstance(d3,PPATCCommitment)
    q = ppatcpk.PPATCpp.order
    d4,nu,z1,z2,z5,s11,s12,s21,s22,s31,s32,s51,s52 = proof

    d1p1 = ppatcpk.commit(z1,s11,s12)
    d1p = d1p1-nu*d1
    d2p1 = ppatcpk.commit(z2,s21,s22)
    d2p = d2p1-nu*d2
    d3p1 = ppatcpk.commit((z1*z2)%q,s31,s32)
    d3p = d3p1-nu*d4-(nu**2)*d3
    d5p1 = ppatcpk.commit(z5,s51,s52)
    d5p = d5p1-nu*d4

    nup = ppatcpk.hashf([d1,d2,d3,d4,d1p,d2p,d3p,d5p,ppatcpk])
    return nu == nup

def multiplicationWithTripletAndCheck(ppatspk,d1,d2,a1,a2,a3,proof,openings):
    ''' This method returns d3 a commitment on the product of the messages
    commited on by d1 and d2.
    (a1,a2,a3) is a multiplicative triplet of commitments (a3 commits on the
    product of the messages commited on by a1 and a2)
    proof is a proof that a1,a2,a3 is a multiplicative triplet
    openings contains the openings of d1-a1 and d2-a2 as messages and opening
    points over the EC
    '''
    #assert isinstance(d1,ppat.ppats.PPATSCommitment)
    #assert isinstance(d2,ppat.ppats.PPATSCommitment)
    assert multiplicationProofCheck(ppatspk,a1,a2,a3,proof)
    (m1,o1),(m2,o2) = openings
    assert ppatspk.verifyOpening(d1-a1,m1,o1)
    assert ppatspk.verifyOpening(d2-a2,m2,o2)
    #h1 = self.h1
    #d3 = (m2*a1.d)+(m1*a2.d)+a3.d+((m1*m2)*h1)
    d3 = ppatspk.multiplicationCommitFromTriplet(a1,a2,a3,m1,m2)
    return d3

"""
def produceMultiplicationTriplets(self,n):
        ''' The method returns a list of n randomly computed multiplication triplet
            The list is of the form
            [((m1,r1,com(m1,r1)),(m2,r2,com(m2,r2)),(m1m2,r3,com(m1m2,r3)),proof)_1,...]
        '''
        start = time.time()
        L = []
        for i in range(n):
            m1 = self.random()
            com1,r1 = self.commit(m1)
            m2 = self.random()
            com2,r2 = self.commit(m2)
            com3,r3 = self.commit(m1*m2)
            proof = self.multiplicationProof(com1,com2,com3,m1,m2,r1,r2,r3)
            L.append(((m1,r1,com1),(m2,r2,com2),(m1*m2,r3,com3),proof))

        end = time.time()
        print "Producing "+str(n)+" multiplication triplets took "+str(end-start)+" sec"
        return L


    def multiplicationWithTripletAndCheck2(self,d1,d2,d3,a1,a2,a3,openings):
        ''' This method returns True if d3 is a commitment on the product of the
        messages commited on by d1 and d2.
            (a1,a2,a3) is a multiplicative triplet of commitments (a3 commits on the
            product of the messages commited on by a1 and a2)
            openings contains the openings of d1-a1 and d2-a2 as messages and
            randomnesses
        '''
        (m1,o1),(m2,o2) = openings
        assert self.verifyCommitment(d1-a1,m1,o1)
        assert self.verifyCommitment(d2-a2,m2,o2)
        #h1 = self.h1
        #d3p = (m2*a1.d)+(m1*a2.d)+a3.d+((m1*m2)*h1)
        d3p = self.multiplicationCommitFromTriplet(a1,a2,a3,m1,m2)
        return d3 == d3p
"""

###################################################################################
######################### Range Proof #############################################
###################################################################################

def base2RangeProof(ppatspk,com,m,r,maxexp,verif = True):
    '''
    This method returns a range proof that com is a commitment on a message m
    with randomness r : the proof assert that m is in [0,2**maxexp[
    The binary representation of m is used to decompose com in 'maxexp'
    commitments on 0 or 1. To each of these commitments, a ZKPoK that the commitment
    commits on 0 or 1 is added.
    verif is a facultative verification of the decomposition
    The range proof is returned in the form of a list containing commitments and
    proofs
    '''

    clap, cla = base2RangeProofPrep(ppatspk,com,m,r,maxexp,verif)
    return clap

def base2RangeProofPrep(ppatspk,com,m,r,maxexp,verif = True):
    '''
    This method returns a range proof that com is a commitment on a message m
    with randomness r : the proof assert that m is in [0,2**maxexp[
    The binary representation of m is used to decompose com in 'maxexp'
    commitments on 0 or 1. To each of these commitments, a ZKPoK that the commitment
    commits on 0 or 1 is added.
    verif is a facultative verification of the decomposition
    The method returns two lists :
    1) the first contains the commitment decomposition
    and the proofs, an item is (facti,comi,proofi) where proofi is a proof that
    comi commits on either 0 or 1 and where facti (typically a power of 2) is
    the coefficient to use when recombining the initial commitment 'com'
    2) another list similar to the first one, but also containing all the
    randomnesses used to compute the commitments ; an item is (facti,comi,bi,ri,
                                                               proofi)
    where bi is the bit commited to and ri the randomness used.
    '''

    if verif :
        assert ppatspk.verifyCommitment(com,m,r)
        assert m<2**maxexp
    b = bin(m)
    bb = b[2:]
    l = len(bb)
    if l<maxexp:
        k = maxexp-l
        for i in range(k):
            bb = '0'+bb
    comlistandproofs = []
    comlistall = []
    order = ppatspk.PPATSpp.order
    totalr = 0
    for i in range(1,maxexp):
        bi = int(bb[maxexp-i-1])
        if verif :
            assert bi == 0 or bi == 1
        facti = 2**i
        comi,ri = ppatspk.commit(bi)
        proofi = verifiabilityProof(ppatspk,comi,bi,ri)
        comlistandproofs.append((facti,comi,proofi))
        comlistall.append((facti,comi,bi,ri,proofi))
        totalr = (totalr+facti*ri)%order

    bfirst = int(bb[-1])
    if verif :
        assert bfirst == 0 or bfirst == 1
    rfirst = r-totalr
    comfirst,rfirst = ppatspk.commit(bfirst,rfirst)
    prooffirst = verifiabilityProof(ppatspk,comfirst,bfirst,rfirst)
    comlistandproofs = [(1,comfirst,prooffirst)] + comlistandproofs
    comlistall = [(1,comfirst,bfirst,rfirst,prooffirst)] + comlistall

    return comlistandproofs, comlistall

def base2RangeProofCheck(ppatspk,com,comlist):
    '''
    Given a commitment an a list 'comlist' containing a commitment decomposition
    in base 2 where each commitment of this decomposition is accompanied with a
    proof that the commitment commits on 0 or 1.
    The method verifies that :
        1) the decomposition is correct which means that every commitment of
        'comlist' sum up to 'com' using multiplicative coefficients stored in
        'comlist'
        2) each proof of 'comlist' is correct which means that every commitment
        of 'comlist' commits on 0 or 1.
    Given that these two conditions are True, the method returns True, otherwise
    it returns a 2-uple where the first element states if the decomposition is
    correct and the second element is a list of the incorrect 3-uple(s)
    (fact,commitment,proof)
    note that the correctness of the coefficient decomposition is checked in the
    method self.base2VerifExpoDecomp()
    '''

    reslist = []
    clist = []
    for facti,comi, proofi in comlist :
        resi = verifiabilityProofCheck(ppatspk,comi,proofi)
        if not resi :
            reslist.append(resi,(facti,comi,proofi))
        clist.append((facti,comi))

    res = verifyCommitmentDecomposition(ppatspk,com,clist)
    if res and reslist == None :
        return True
    else :
        return res,reslist

def verifyCommitmentDecomposition(ppatspk,com,comlist):
    '''
    verify that com is the sum of the commitment in comlist multiplied by a factor
    comlist is a list of tuples (com_i,fact_i) of commitments and factors
    '''
    newcom = CommitmentRecompose(ppatspk,comlist)
    return newcom == com

def CommitmentRecompose(ppatspk,comlist):
    ''' Given a list of commitments and a list of coefficient, the method returns
    the sum of the product of the commitments by their coeficients
    '''
    newcom,r = ppatspk.commit(0,0)
    for coefi,comi in comlist :
        newcom = newcom+coefi*comi
    return newcom

def base2VerifExpoDecomp(ppatspk,comlist,maxexp):
    '''
    This method checks that given a 'comlist' containing (facti,comi,proofi) ;
    facti are correct coefficients : facti = 2**i for i in range(0,maxexp)
    '''
    fact = 2**maxexp
    order = ppatspk.PPATSpp.order
    fact2 = order-fact
    resList = []
    k = len(comlist)
    fa = 1
    for i in range(k) :
        j = k-i-1
        facti = comlist[j][0]
        if j == 0 :
            res = facti == fact2
        else :
            res = facti == fa
            fa = 2*fa
        if res == False :
            resList.append((res,facti))
    return (resList == [],resList)

def geqProof(ppatspk,com1,m1,r1,com2,m2,r2,maxexp):
    '''
    This method returns a range proof that the commitment com3 on m1-m2 is in
    [0,2**maxexp[, com3 is obtained by substracting com1-com2
    '''
    assert m1 >= m2
    order = ppatspk.PPATSpp.order
    com3 = com1-com2
    m3 = (m1-m2)%order
    r3 = (r1-r2)%order
    assert ppatspk.verifyCommitment(com3,m3,r3)

    clist,comlist =  gtzero(ppatspk,com3,m3,r3,maxexp)
    assert clist[0][0] == 0
    rcond = clist[0][1]
    geqproof = comlist, rcond
    return geqproof

def geqProofCheck(ppatspk,com1,com2,geqproof,maxexp,verifDecomp=True):
    comlist, rcond = geqproof
    com3 = com1-com2
    comcond = comlist[0][1]
    res1 = ppatspk.verifyCommitment(comcond, 0, rcond)
    res2 = base2RangeProofCheck(ppatspk,com3,comlist)
    if verifDecomp :
        comlist2 = comlist[1:]
        res3 = base2VerifExpoDecomp(ppatspk,comlist2,maxexp)
        order = ppatspk.PPATSpp.order
        res4 = comlist[0][0] == order - 2**maxexp
        return res1 and res2 and res3 and res4
    else :
        return res1 and res2

def gtzero(ppatspk,com,m,r,maxexp):
    ''' This method returns a commtiment decomposition of the commitment com
    where :
    if order is the size of the field, m is a message in ]-2**maxexp, 2**maxexp[
    '''

    def decompCom(m,r,com,base):
        '''base is a list of pairs (b,e) where the b-s are bases in decreasing order
        and the e-s are the maximum bound for the exponent associated with b
        '''

        assert ppatspk.verifyCommitment(com,m,r)
        order = ppatspk.PPATSpp.order
        mlist = multibaseDecomp(m,base)
        comlist = []
        rt = 0
        for (x,fact) in mlist :
            com,rp = ppatspk.commit(x)
            comlist.append((x,rp,fact,com))
            rt = (rt + rp*fact)%order

        if not comlist == []:
            lastx,lastr,lastfact,lastcom = comlist.pop(-1)
            newr = r-rt+lastr
            newcom, newr = ppatspk.commit(lastx,newr)
            comlist.append((lastx,newr,lastfact,newcom))

        return comlist

    fact = 2**maxexp
    order = ppatspk.PPATSpp.order
    fact2 = order-fact
    mm = m%order
    assert mm<fact  or mm>=fact2
    base = [(fact2,1,1,1),(2,1,0,maxexp-1)]
    clist = decompCom(mm,r,com,base)
    comlist = []
    for mi,ri,facti,comi in clist :
        vproofi = verifiabilityProof(ppatspk,comi,mi,ri)
        comlist.append((facti,comi,vproofi))

    return clist,comlist

def multibaseDecomp(m,base):
    ''' base is a list composed of [(b,maxval,minexp,maxexp)]
    for each tuple :
    - b is the base
    - maxval is a range from 0 to maxval in which coefficient can be taken
    - minexp is the minimum exponent possible for b
    - maxexp is the maximum coefficient possible for b
    - at the end of the method,  m = sum(m_ij*b_j**(e_ij)) for m_ij between
    0 and maxval_j, e_ij between minexp_j and maxexp_j where j ranges for
    the elements in the list base

    the method returns a list of the tuples (m_ij,b_j**(e_ij))
    '''
    newm = m
    mlist = []
    for (b,maxval,minexp,maxexp) in base :
        expo = maxexp
        while expo >= minexp:
            mult = maxval
            fact = b**expo
            mp = -1
            while mult > 0 and mp == -1 :
                mf = mult*fact
                if newm >= mf :
                    mp = mult
                    newm = newm-mf
                mult = mult - 1
            if mp == -1:
                mlist.append((0,fact))
            else :
                mlist.append((mp,fact))
            expo = expo - 1
    #check
    mcheck = 0
    for a,b in mlist:
        mcheck = mcheck +a*b
    assert mcheck == m # invalid decomposition occured

    return mlist

def splitCommitment(ppatspk,com,m,a):
    ''' This method is a simpler version of self.decomposeCommitment()
    Assuming that commitment com commits on the message m and has opening a.
    The method decomposes com in two parts com1,com2 such that
    com = com1+com2. com2 is a commitment on 0, com1 is a commitment on m

    The output of the method is a list of two elements : the two commitments
    com1 and com2 together with the randomness and opening used in each.

    Remark : The point of doing this is, in some way, to modify the randomness
    used in the commitment. For example, suppose that you know the opening
    of the commitment but not the randomness used in the commitment. With
    this method, you can create another commitment that commits on the same
    value but now, you know the randomness used in it. This is usefull in
    order to produce set membership proofs.
    '''
    g = ppatspk.PPATSpp.g
    Jcoord = ppatspk.PPATSpp.Jcoord
    com1,r1 = ppatspk.commit(m)
    ECG = g.ECG
    a1t = oEC.mul_comb2_EFp2(ECG,r1,ppatspk.precomp_g,Jcoord)
    a1 = oEC.toEFp2(ECG,a1t,Jcoord)
    com2d = com.d-com1.d
    com2 = ppat.ppats.PPATSCommitment(com2d,ppatspk)
    a2 = a-a1

    comlist = [(m,r1,a1,com1),(0,None,a2,com2)]

    return comlist
