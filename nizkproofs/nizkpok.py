# -*- coding: utf-8 -*-

from Crypto.Random.random import randint
import ppat.ppats
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

def consistencyProofCheck(ppatspk,c,proof):
    ''' Checks the validity of the proof in regards to c
    '''
    #assert isinstance(c,ppats.PPATSCiphertext)
    nu,zm,zr,zs = proof
    cz = ppatspk.encrypt(zm,zr,zs)
    cp = cz-(c*nu)

    nup = ppatspk.hashf([ppatspk.PPATSpp,ppatspk,c,cp])
    return nup == nu

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

"""
def baseComp(self):
    ''' OBSOLETE
    #TODO : correct the method
    This method is used by default in the methods decomposecommitment().
    It provides a base.
    '''

    q = self.PPATSpp.q
    q2 = int((q-1)/2)
    q3 = q2+1
    '''
    lg = len(bin(q2))
    log = emath.log
    def f(u,lg):
        w = u*((log(u))**2)-(10*lg)
        return w
    a = fsolve(f,50,lg)
    ap = int(round(a))
    expo = int(round((log(2)/(log(ap)))*lg))
    assert ap**expo > q2
    L = [(q3,1,1,1),(ap,ap-1,0,expo)]
    '''
    L = [(q3,1,1,1),(100000,99999,0,10)]
    return L
"""

"""
def splitCommitment(self,com,m,a):
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
    g = self.PPATSpp.g
    com1,r1 = self.commit(m)
    EFq2 = g.EFq
    a1t = fME.mul_EFp2(r1,EFq2,self.precomp_g)
    #a1 = r1*g
    a1 = EFq2.toEFp2(a1t)
    com2d = com.d-com1.d
    com2 = PPATSCommitment(com2d,self)
    a2 = a-a1

    comlist = [(m,r1,a1,com1),(0,None,a2,com2)]

    return comlist
"""

"""
def decomposeCommitment(self,m,a,com,base = None, pos = 0 ):
        '''
           'base' is a list of pairs (b,e) where the b-s are bases in decreasing order
           and the e-s are the maximum bound for the exponent associated with b
           We assume that the first value of base is ((order-1)/2)+1 whith index in {0,1}
        '''
        #assert self.verifyOpening(com,m,a)
        order = self.PPATSpp.order
        if base == None :
            base = self.baseComp()
        mlist = self.multibaseDecomp(m,base)
        comlist = []
        rt = 0
        g = self.PPATSpp.g
        h = self.PPATSpp.h
        #h1 = self.h1
        EFq = h.EFq
        EFq2 = g.EFq

        for (x,fact) in mlist :
            newcom,rp = self.commit(x)
            nrp = (rp*fact) %order
            #ap = rp*g
            apt = fME.mul_EFp2(rp,EFq2,self.precomp_g)
            ap = EFq2.toEFp2(apt)
            comlist.append((x,rp,ap,fact,newcom))
            rt = (rt + nrp)%order

        if not comlist == []:
            '''
            the following replaces the first commitment of comlist by a new one
            that is on the same message but with another randomness so that the
            equation
            com = sum(fact_i*com_i) is satisfied
            to do that we build com_1 as m_1*h1 + r_1*h
            where fact_1*r_1 = r - sum(fact_i*r_i) on i>1
            r_1 cannot be computed because r is unknown. However one can build
            r_1*h ('newrh') since r*h is known.
            Note that fact_1 = ((order-1)/2)+1 and its inverse is 2 mod order.
            We then compute r_1*h from the equation
            sum(fact_i*r_i*h) = r*h by isolating fact_1*r_1*h and by multiplying
            each side by 2.
            In the same way, one computes the opening 'newa'
            '''
            firstx,firstr,firsta,firstfact,firstcom = comlist.pop(pos)
            mh1t = fME.mul_EFp(m,EFq,self.precomp_h1)
            mh1 = EFq.toEFp(mh1t)
            #randh = com.d - m*h1 # r*h
            randh = com.d - mh1
            newr = (rt-firstfact*firstr) % order # sum(fact_i*r_i) for i>1
            att = fME.mul_EFp2(newr,EFq2,self.precomp_g)
            at = EFq2.toEFp2(att)
            #at = newr*g
            htt = fME.mul_EFp(newr,EFq,self.precomp_h)
            ht = EFq.toEFp(htt)
            #ht = newr*h
            Zq = Field.Field(order)
            ff = Zq.elem(firstfact)
            iff = ff.invert().val
            newa = iff*(a-at) # r_1*g
            newrh = iff*(randh - ht) # r_1*h
            firstxh1t = fME.mul_EFp(firstx,EFq,self.precomp_h1)
            firstxh1 = EFq.toEFp(firstxh1t)
            #newcomd = newrh + firstx*h1 #r_1*h + m_1*h1
            newcomd = newrh+firstxh1
            newcom = PPATSCommitment(newcomd,self)

            comlist = comlist[:pos]+[(firstx,None,newa,firstfact,newcom)] + comlist[pos:]

        return comlist



def rangeProof(self,com,m,r=None,a=None,base =None):
        ''' This method returns a ZK range proof on the commitment on the
            message m using randomness r (or the opening a).
            base is a base in which the commitment will be decomposed.
            The range proof is made of several set membership proofs on a list of
            commitments.
            There are two cases :
                - if the randomness is given, all the randomnesses used in the
                commitments from the commitment decomposition, are known
                - if only the opening is given, then at least the randomness of
                one commitment of the commitment decomposition, is unknown. In this
                case, this commitment has to be open and thus does not require a
                set membership proof

            To sum up, the output of this method is :
                - a commitment list, resulting from the commitment decomposition
                obtained through the method self.decomposeCommitment*()
                - the same commitment list for which set membership proofs have
                been added for each commitment (but perhaps one of them (see above))
        '''
        assert not (m == None and a == None) # one of the two has to be something
        g = self.PPATSpp.g
        if not r == None :
            if not a == None :
                assert a == r*g

            comlist = self.decomposeCommitment2(m,r,com,base)
            comlistandproof = []
            m0,r0,fact0,com0 = comlist.pop(0)
            a0 = r0*g
            comlistandproof.append((m0,a0,fact0,com0))
            for mi,ri,facti,comi in comlist :
                msproofi = self.membershipProof(comi,mi,ri)
                comlistandproof.append((facti,comi,msproofi))
            comlist = [(m0,r0,a0,fact0,com0)]+comlist
        else :
            assert not a == None
            comlist = self.decomposeCommitment(m,a,com,base)
            comlistandproof = []
            m0,r0,a0,fact0,com0 = comlist.pop(0)
            comlistandproof.append((m0,a0,fact0,com0))
            for mi,ri,ai,facti,comi in comlist :
                msproofi = self.membershipProof(comi,mi,ri)
                comlistandproof.append((facti,comi,msproofi))
            comlist = [(m0,r0,a0,fact0,com0)]+comlist

        return comlist,comlistandproof

    def rangeProofCheck(self,com,comlistandproof,checkfirst = True):
        ''' Given a commitment and a list of commitments and set membership proofs,
        this method verifies that :
            - each set membership proof is correct
            - the commitment decomposition is correct in regards to the commitment
            com
            - if checkfirst is True, it also checks that the first commitment of the
            commitment decomposition has a valid opening and that the message is
            either 0 or 1. Otherwise it does not check it.

            The output of the method is a logical AND of this three verifications.
        '''
        comlist = []
        clp2 = comlistandproof+[] #copy of the range proof
        if checkfirst :
            m0,a0,fact0,com0 = clp2.pop(0)
            assert self.verifyOpening(com0,m0,a0) # first commitment is well formed
            assert m0 == 0 or m0 == 1 # first commitment is on 0 or 1
            comlist.append((fact0,com0))

        for i in range(len(clp2)) :
            facti,comi,msproofi = clp2[i]
            comlist.append((facti,comi))
            assert self.membershipProofCheck(comi,msproofi)# membership proof accepted

        result = self.verifyCommitmentDecomposition(com,comlist)
        #print result
        return result

    def splitCommitment(self,com,m,a):
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
        g = self.PPATSpp.g
        com1,r1 = self.commit(m)
        EFq2 = g.EFq
        a1t = fME.mul_EFp2(r1,EFq2,self.precomp_g)
        #a1 = r1*g
        a1 = EFq2.toEFp2(a1t)
        com2d = com.d-com1.d
        com2 = PPATSCommitment(com2d,self)
        a2 = a-a1

        comlist = [(m,r1,a1,com1),(0,None,a2,com2)]

        return comlist

    """

###################################################################################
######################### Membership Proof ########################################
###################################################################################
"""
    def membershipProof(self,com,m,r,signatureSet,v=None,s=None,t=None,w=None):
        '''
        Assuming com is a commitment on m using randomness r, the method returns a
        set membership proof that the message m is in the set for which
        signatureSet (see signatureSet.py) contains valid signatures.
        v,s,t and w are the randomness used in the proof, using the method
        self.random() if they are not provided.

        The ZK proof used is the one provided by Camenish et al. ASIACRYPT 2008 in
        " Efficient Protocols for Set Membership and Range Proofs" p 241

        The protocol uses optimized operations.
        '''

        #assert self.verifyCommitment(com,m,r)

        if v == None:
            v = self.random()
        if s == None:
            s = self.random()
        if t == None:
            t = self.random()
        if w == None:
            w = self.random()
        #notations
        sigpk, sigHash, signatureDic = signatureSet.publicSignatureKey, signatureSet.signatureHash, signatureSet.signatureDic
        assert m in signatureDic
        order = self.PPATSpp.order
        e = self.PPATSpp.e
        h = self.PPATSpp.h
        h1 = self.h1
        Pair = self.PPATSpp.Pair
        EFq2 = self.PPATSpp.g.EFq
        EFq = h.EFq

        psi = self.PPATSpp.psi
        #psih1 = psi(h1)
        ehgt  = self.ehgt

        A = signatureDic[m]
        At = A.toTupleEFp2()
        #V = v*A
        Vt = EFq2.mulFp2(At,v)
        V = EFq2.toEFp2(Vt)

        ht = h.toTupleEFp()
        hst = EFq.mulFp(ht,-s)
        hs = EFq.toEFp(hst)

        #commitment

        intert = Pair.simpleexpo2(ehgt,t)

        e1 = Pair.toTuple(e(hs,psi(V)))
        at = Pair.mul2F12(e1,intert)
        a = Pair.toFp12elem(at)

        h1t = h1.toTupleEFp()
        sh1 = EFq.mulFp(h1t,s)
        wh = EFq.mulFp(ht,w)
        Dvt = EFq.taddFp(sh1,wh)
        Dv = EFq.toEFp(Dvt)
        #D = PPATSCommitment(s*h1+w*h,self) # D = s*h1 + w*h
        D = PPATSCommitment(Dv,self) # D = s*h1 + w*h
        #challenge
        nu = self.hashf([self,com,sigHash,V,D,a])
        #response
        zm = (s-nu*m)%order
        zr = (w-nu*r)%order
        zv = (t-nu*v)%order

        proof = V,nu,zm,zr,zv
        return proof

    def membershipProofCheck(self,com,proof,signatureSet):
        ''' Given a commitment and a set membership proof of this commitment, the
            method checks that the proof is correct.
            The set membership proof is verified in respect to self.signatureSet
            the set of valid signatures for which the commitment commits on a valid
            element.

            The method returns True if the verification succeeds.

            The ZK proof used is the one provided by Camenish et al. ASIACRYPT 2008 in
            " Efficient Protocols for Set Membership and Range Proofs" p 241

            The protocol uses optimized operations.
        '''
        V,nu,zm,zr,zv = proof
        #notations
        sigpk, sigHash = signatureSet.publicSignatureKey, signatureSet.signatureHash
        h = self.PPATSpp.h
        h1 = self.h1
        e = self.PPATSpp.e
        psi = self.PPATSpp.psi
        #psih1 = psi(h1)
        Pair = self.PPATSpp.Pair
        #EFq2 = self.PPATSpp.g.EFq
        EFq = h.EFq
        ehgt  = self.ehgt



        #h.toJcoord()
        #h1.toJcoord()
        #t1 = time.time()
        d = com.d
        #d.toJcoord()
        dt = d.toTupleEFp()
        h1t = h1.toTupleEFp()
        ht = h.toTupleEFp()
        #y1 = d*nu
        #y2 = h1*zm
        #y3 = h*zr

        y1 = EFq.mulFp(dt,nu)
        #y1p = nu*d
        y2 = EFq.mulFp(h1t,zm)
        #y2p = zm*h1
        y3 = EFq.mulFp(ht,zr)
        #y3p = h*zr
        #print y3p, EFq.toEFp2(y3) ,  EFq.toEFp2(y3) == y3p

        x1 = EFq.taddFp(y1,y2)
        #x1p = y1p+y2p
        Dvt = EFq.taddFp(x1,y3)
        #Dvtp = x1p+y3p
        #print EFq.toEFp2(Dvt) ,Dvtp,  EFq.toEFp2(Dvt) == Dvtp
        Dval = EFq.toEFp(Dvt)
        #Dval.toAffine()
        #h.toAffine()
        #h1.toAffine()
        #d.toAffine()
        #Dval2 = nu*com.d+zm*h1+zr*h
        Dp = PPATSCommitment(Dval,self)
        #print Dval,Dval2, Dval == Dval2
        #t2 = time.time()
        #ap = ((e(V,psiy))**nu)*((e(V,psih1))**(-zm))*(egh1**zv)
        #inter = Pair.toFp12elem(Pair.simpleexpo2(t_egh1,zv))
        intert = Pair.simpleexpo2(ehgt,zv)
        #t3 = time.time()
        #ap = (e(nu*V,sigpk))*(e(-zm*V,h1))*(egh1**zv)
        #ap = (e(nu*V,sigpk))*(e(-zm*V,h1))*inter
        #Vt = V.toTupleEFp2(0)
        #nVt = EFq.mulFp(Vt,nu,0)
        #zVt = EFq.mulFp(Vt,-zm,0)
        sigpkt = sigpk.toTupleEFp()
        spknt = EFq.mulFp(sigpkt,nu)
        zmht = EFq.mulFp(ht,-zm)
        spkn = EFq.toEFp(spknt)
        zmh = EFq.toEFp(zmht)

        #nV = EFq.toEFp(nVt,0)
        #zV = EFq.toEFp(zVt,0)
        #e1 = Pair.toTuple(e(nu*V,sigpk))
        #e2 = Pair.toTuple(e(-zm*V,h1))
        #e1 = Pair.toTuple(e(nV,sigpk))
        e1 = Pair.toTuple(e(spkn,psi(V)))
        #e2 = Pair.toTuple(e(zV,h1))
        e2 = Pair.toTuple(e(zmh,psi(V)))
        apt = Pair.mul2F12(Pair.mul2F12(e1,e2),intert)
        ap = Pair.toFp12elem(apt)
        #t4 = time.time()

        nup = self.hashf([self,com,sigHash,V,Dp,ap])
        #t5 = time.time()

        return nu == nup#,t2-t1,t3-t2,t4-t3,t5-t4
        #return nu == nup


    '''
    The 3 following methods are designed to save and load a particular PPATS public
    key in a file using the module pickle.
    The goal is to save the public keys h1 and g1. The PPATS public parameters have
    to be saved separately.
    '''
    def toDump(self):
        #dobjectppatspp = self.PPATSpp.toDump()
        h1x =  self.h1.x.val
        h1y = self.h1.y.val
        g1x = self.g1.x.poly.coef[0].val,self.g1.x.poly.coef[1].val
        g1y = self.g1.y.poly.coef[0].val,self.g1.y.poly.coef[1].val

        #return (dobjectppatspp,(g1x,g1y),(h1x,h1y))
        return ((g1x,g1y),(h1x,h1y))

    def dump(self,filename):

        L = self.toDump()
        f = open(filename,'w')
        pickle.dump(L,f)
        f.close()

    def load(self,filename,ppatspp):
        f = open(filename)
        L = pickle.load(f)
        f.close()
        #dobj_ppatspp, dobj_g1, dobj_h1 = L
        dobj_g1, dobj_h1 = L
        #ppatspp = PPATSPublicParameters.rebuild(dobj_ppatspp)
        #ppatspk = PPATSPublicKey.rebuild(ppatspp,dobj_g1, dobj_h1)
        #return ppatspk
        #self.rebuild(ppatspp,dobj_g1, dobj_h1)

    #def rebuild(self,ppatspp,dobj_g1, dobj_h1):
        self.PPATSpp = ppatspp
        h1x,h1y = dobj_h1
        EF = ppatspp.h.EFq
        #Fq = EF.F
        h1 = EF.elem(h1x,h1y)
        EFq = ppatspp.g.EFq
        Fq2 = EFq.F
        g1x,g1y = dobj_g1
        g1x0,g1x1 = g1x
        g1y0,g1y1 = g1y
        g1px = g1x0*Fq2.unit()+g1x1*Fq2.one()
        g1py = g1y0*Fq2.unit()+g1y1*Fq2.one()
        g1 = EFq.elem(g1px,g1py)
        #ppatspk = PPATSPublicKey(ppatspp,g1,h1)
        self.h1 = h1
        self.g1 = g1
        print "public keys g1,h1 replaced"

    def storeSignatureSet(self,sigpk,signatureSet,filename):
        '''
        This method allows one to save a signature set into a file 'filename'.
        The method also saves the public key that is needed to perform the verific-
        ation on a set membership proof.
        '''
        sigpkx = int(sigpk.x.val)
        sigpky = int(sigpk.y.val)
        sigdict = signatureSet.copy()
        for key in sigdict.keys() :
            ECpoint = sigdict[key]
            ECx = int(ECpoint.x.poly.coef[0].val), int(ECpoint.x.poly.coef[1].val)
            ECy = int(ECpoint.y.poly.coef[0].val), int(ECpoint.y.poly.coef[1].val)
            sigdict[key] = (ECx,ECy)

        #h1x = self.h1.x.val
        #h1y = self.h1.y.val

        #toStore = ((h1x,h1y),(sigpkx,sigpky),sigdict)
        #toStore = ((sigpkx,sigpky),sigdict)
        toStore = marshal.dumps(((sigpkx,sigpky),sigdict))

        f = open(filename,'w')
        #pickle.dump(toStore,f)
        marshal.dump(toStore,f)
        f.close()

    def buildSignatureSet(self,a,b,x):
        ''' This method returns a signature key y = x*h in G1
            and a dictionnary containing signatures for each integer
            between a and b.
            The signature is (1/(x+i))*g in G2 for a<=i<=b.

            The signature set construction used is the one provided by Camenish
            et al. ASIACRYPT 2008 in " Efficient Protocols for Set Membership and
            Range Proofs" p 241
        '''
        g = self.PPATSpp.g
        h = self.PPATSpp.h
        #psi = self.PPATSpp.psi
        y = x*h
        #psiy = psi(y)
        Zq = Field.Field(self.PPATSpp.q)
        S = {}
        for i in range(a,b+1):
            xi = Zq.elem(x+i)
            xiinv = xi.invert() # multiplicative inverse of x+i mod q
            A = (xiinv.val)*g
            S.setdefault(i)
            S[i] = A

        return y,S

    def loadSignatureSet(self,filename):
        '''
           This method loads a signature set from a file and rebuilds it.
           It also rebuilds the public key of the signature set that is
           used in the set membership proof verification.
        '''
        EFq = self.g1.EFq
        Fq2 = EFq.F
        EF = self.h1.EFq
        #Fq = EF.F
        f = open(filename,'r')
        #toLoad = pickle.load(f)
        toLoad = marshal.loads(marshal.load(f))
        f.close()
        uy,udict = toLoad
        yx,yy = uy
        sigpk = EF.elem(yx,yy)
        #h1x,h1y = uh1
        #h1 = EF.elem(h1x,h1y)
        sigdict = udict.copy()
        for key in udict.keys() :
            px,py = udict[key]
            pvx0, pvx1 = px
            pvy0, pvy1 = py
            ppx = pvx0*Fq2.unit()+pvx1*Fq2.one()
            ppy = pvy0*Fq2.unit()+pvy1*Fq2.one()
            sigdict[key] = EF.elem(ppx,ppy)

        return sigpk,sigdict


    def multibaseDecomp(self,m,base):
        ''' base is a list composed of [(b,maxval,minexp,maxexp)]
        for each tuple :
            b is the base
            maxval is a range from 0 to maxval in which coefficient can be taken

            minexp is the minimum exponent possible for b

            maxexp is the maximum coefficient possible for b

            at the end of the method,  m = sum(m_ij*b_j**(e_ij)) for m_ij between
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

    def baseComp(self):
        ''' OBSOLETE
            #TODO : correct the method
            This method is used by default in the methods decomposecommitment().
            It provides a base.
        '''

        order = self.PPATSpp.order
        q2 = int((order-1)/2)
        q3 = q2+1
        '''
        lg = len(bin(q2))
        log = emath.log
        def f(u,lg):
            w = u*((log(u))**2)-(10*lg)
            return w
        a = fsolve(f,50,lg)
        ap = int(round(a))
        expo = int(round((log(2)/(log(ap)))*lg))
        assert ap**expo > q2
        L = [(q3,1,1,1),(ap,ap-1,0,expo)]
        '''
        L = [(q3,1,1,1),(100000,99999,0,10)]
        return L


    def base2(self,maxexp):
        return [(2,1,0,maxexp)]
"""
