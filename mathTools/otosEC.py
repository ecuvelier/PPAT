# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""
"""
########################################################################

This module contains Optimized Tools for Operations in Specific
Elliptic Curves (OTOSEC)

Mainly, we target the elliptic curves over prime Field F_p (EFp), and the extension
fields F_p2 (EFp2), as well as operations in F_p^12 (Fp12).
Fp12 is towered as follows:
    Fp12 = Fp6/(X**2-xi)
    Fp6 = Fp2/(Y**3-xi)
    Fp2 = Fp(i**2+1), the complex field
    xi has niether a cubic nor a square root in Fp2

The elliptic curves targeted are BN-curves of equation y**2 = ax**3+b where
b = c**4+d**6 (see [2] below) ; we have that xi = c**2+d**3*i
(where 'i' is the imaginary number)

A point on these curves will be given by its x, y (and z if Jacobian)
coordinates in the form of a tuple. In affine coordinates, the two values
x and y are complemented with a boolean Pinf set to true if the point is
the point at infinity. In this case, x and y are irelevant.

The prerequisites for the functions below are strong to reduce the number
of verifications inside the functions and thus fasten the execution.

Algorithm 'comb2' of [1] is used to perform fast scalar multiplications when
precomputation is available.

References:
[1] Haustenne, L.; De Neyer, Q.; Pereira, O. & others Elliptic Curve Cryptography
in JavaScript. IACR Cryptology ePrint Archive, 2011, 2011, 654

[2] Pereira, G. C.; Simplicio Jr, M. A.; Naehrig, M. & Barreto, P. S. A family of
implementation-friendly BN elliptic curves Journal of Systems and Software,
Elsevier, 2011, 84, 1319-1326

[3] Aranha, D. F.; Karabina, K.; Longa, P.; Gebotys, C. H. & López, J. Faster
explicit formulas for computing pairings over ordinary curves Advances in
Cryptology--EUROCRYPT 2011, Springer, 2011, 48-68
"""

import gmpy
import ellipticCurve
import tools.utils as utils
import field
import math

################# Generic ##############################################

def mulECP(ECG,P,alpha,sq= False, Jcoord=False):
    ''' multiplication by a scalar or FieldElem
    Assuming P is an ECPoint represented by
    - a 3-uple (in EFp in both Affine or Jacobian coordinates),
    - 5-uple or 6-uple (in EFp2 in Affine or Jacobian coordinates respectively)
    and alpha an integer
    sq is False by default assuming P is in EFp, and True if P is in EFp2
    Jcoord indicates the use of Jacobian (True) or Affine (False) coordinates
    '''
    #p = ECG.F.char
    #if abs(alpha)>=p:
    #    alpha = alpha % p
    if alpha == 0 :
        # multiplying by zero returns the point at infinity
        zero = gmpy.mpz(0)
        one = gmpy.mpz(1)
        if Jcoord :
            if not sq :
                return zero,one,zero
            else :
                return zero, zero, zero, one, zero, zero
        else :
            if not sq :
                return zero,zero,True
            else :
                return zero,zero,zero,zero,True
    elif alpha<0:
        if not sq :
                Xq,Yq,Zq = dbleAndAdd(ECG,P,-alpha,daddEFp,doubleEFp,Jcoord)
                return Xq,-Yq,Zq
        else :
            if Jcoord :
                Xq0,Xq1,Yq0,Yq1,Zq0,Zq1 = dbleAndAdd(ECG,P,-alpha, daddEFp2, doubleEFp2, Jcoord)
                return Xq0,Xq1,-Yq0,-Yq1,Zq0,Zq1
            else :
                Xq0,Xq1,Yq0,Yq1, Qinf = dbleAndAdd(ECG,P,-alpha, daddEFp2, doubleEFp2, Jcoord)
                return Xq0,Xq1,-Yq0,-Yq1, Qinf
    else :
        if not sq :
            return dbleAndAdd(ECG,P,alpha,daddEFp,doubleEFp,Jcoord)
        else :
            return dbleAndAdd(ECG,P,alpha,daddEFp2,doubleEFp2,Jcoord)

def dbleAndAdd(ECG,P,alpha,addition,doubling,Jcoord = False):
    '''return alpha*P using double and add technique in EFp
    - assuming ECG is a EC group
    - P is a 3-uple
    - assuming alpha is an integer
    - addition is the addition operation between two points and
    - doubling is the doubling operation "" ""
    they both take as first argument ECG, the EC group, and as
    last argument a boolean Jcoord.
    You might call this function by replacing
    ~ addition by daddEFp or daddEFp2
    ~ doubling by doubleEFp or doubleEFp2
    -Jcoord is a boolean set to true if the Jacobian coordinates
    are used and false if affine coordinates are used
    '''

    if alpha == 1 :
        return P
    elif alpha%2 == 1 :
        Q = dbleAndAdd(ECG,P,(alpha-1)/2,addition,doubling,Jcoord)
        return addition(ECG,P,doubling(ECG,Q,Jcoord),Jcoord)
    elif alpha%2 == 0 :
        Q = dbleAndAdd(ECG,P,alpha/2,addition,doubling,Jcoord)
        return doubling(ECG,Q,Jcoord)

def squareAndMultiply(F,x,u,multiply,square,tab=None):
    ''' Return x**u using square and multiply
    - assuming x belongs to F and u is positive integer
    - multiply is the multiplication algorithm
    - square is the squaring algorithm
    '''
    if u == 0 :
        return F.one()
    elif u == 1 :
        return x
    elif u%2 == 1 :
        y = squareAndMultiply(F,x,(u-1)/2,multiply,square,tab)
        return multiply(F,x,square(F,y,tab),tab)
    elif u%2 == 0 :
        y = squareAndMultiply(F,x,u/2,multiply,square,tab)
        return square(F,y,tab)

def mul_comb2(alpha,tab,dadd,dble,inf):
    '''
    Fast scalar multiplication using comb2 see [1]
    - alpha is the multiplicand
    - tab contains
    ~ the precomputed values of the point to be multiplicated
    ~ w is the length of the windows
    ~ m is the bit lenght of alpha
    ~ d is the number of windows w in m (rounded down integer)
    ~ e is the half of d (rounded down integer)
    - dadd is the addition operation to use, typically daddEFp or daddEFp2
    - dble is the doubling operation to use, typically doubleEFp or doubleEFp2
    - inf is a method that returns true if the point at infinity is given as input
    '''
    precomptab,w,m,d,e = tab

    def rearange(t):
        k = len(t)
        l = len(t[0])
        newt = ()
        for j in range(l):
            ent = ''
            for i in range(k):
                ind = t[i][j]
                ent = ent+ind
            newt = (ent,)+newt
        return newt

    tabk = rearange(utils.decompBin(alpha,d,m)) #TODO: check if correct
    Q = precomptab[0][0] # Q = inf
    for i in range(e-1,-1,-1):
        Q = dble(Q)
        Ki = tabk[i]
        iKi = int(Ki,2)
        Kie = tabk[i+e]
        iKie = int(Kie,2)
        P1 = precomptab[iKi][0]
        P2 = precomptab[iKie][1]
        if inf(P1) and inf(P2) :
            pass
        elif inf(P1) and not inf(P2) :
            Q = dadd(Q,P2)
        elif not inf(P1) and inf(P2) :
            Q = dadd(Q,P1)
        else :
            Q = dadd(dadd(Q,P1),P2)
    return Q

def precomp_comb2(w,m,P,add,mul):
    '''
    Return a table containing precomputed multiple of P that is used to compute
    fast scalar multiplications of P using the comb2 method see [1]
    - w is the length of the windows
    - m is the bit lenght of alpha
    - add is the addition operation, typically addEFp or addEFp2
    - mul is the scalar multiplication, typically mulECP with appropriate parameters
    '''
    d = int(math.ceil(float(m)/w))
    Pstar = ()
    for i in range(w-1,-1,-1):
        ent = mul(P,2**(i*d))
        Pstar = Pstar + (ent,)
    e = int(math.ceil(d/2))
    tablet = ()
    e2 = (2**e)

    def dotprod(a,b,add,mul):
        assert len(a)==len(b) and len(a)>0
        res = mul(b[0],int(a[0]))
        for i in range(1,len(a)):
            res = add(res,mul(b[i],int(a[i])))
        return res

    for i in range(2**w):
        bi = utils.decompBin(i,1,w)
        ent1 = dotprod(bi,Pstar,add,mul)
        ent2 = mul(ent1,e2)
        tablet = tablet+((ent1,ent2),)
    return tablet

########################################################################
################# Curve over Fp ########################################
########################################################################

def addEFp(ECG,P1,P2,Jcoord=False):
    ''' This method returns  Q = P1+P2
    - if Jcoord is True : a 3-uple Qx,Qy,Qz = Q
    - if not : a 3-uple Qx,Qy,Qinf where Q=(Qx,Qy) and Qinf is boolean
    assuming P1,P2 are 3-uple of values in Fp representing EC points,
    where
    - if Jcoord is true, P1,P2 are 3-uple of x-,y-, and z- coordinates
    - if Jcoord is false, P1,P2 are 3-uple of x-, y- coordinates plus a
    boolean Pinf telling if P is the point at infinity
    assuming ECG is an elliptic curve over a field Fp
    '''

    if Jcoord :
        Xp1,Yp1,Zp1 = P1
        Xp2,Yp2,Zp2 = P2
        if Zp1 == 0:
            return Xp2,Yp2,Zp2
        elif Zp2 == 0:
            return Xp1,Yp1,Zp1
        else :
            T1 = Zp1**2
            T2 = Zp2**2
            A = Xp1*T2 # Xp1*Zp2**2
            B = Xp2*T1 # Xp2*Zp1**2
            C = Yp1*T2*Zp2 # Yp1*Zp2**3
            D = Yp2*T1*Zp1 # Yp2*Zp1**3
            if A == B and C == D :
                return doubleEFp(ECG,P1,T1)
            else :
                #P1 != P2
                if Xp1 == Xp2 :
                    # P1 and P2 have same x coordinate (but not same y)
                    # => P1+P2 = O
                    zero = gmpy.mpz(0)
                    return zero,gmpy.mpz(1),zero
                else :
                    return daddEFp(ECG,P1,P2,(T1,T2,A,B,C,D),Jcoord)
    else:
        #Affine coordinates used
        Xp1,Yp1,P1inf = P1
        Xp2,Yp2,P2inf = P2
        if P1inf :
            return Xp2,Yp2,P2inf
        elif P2inf :
            return Xp1,Yp1,P1inf
        elif P1==P2:
            return doubleEFp(ECG,P1,Jcoord=True)
        else:
            # P1!=P2
            if Xp1 == Xp2 :
                return gmpy.mpz(0),gmpy.mpz(1),True
            else:
                return daddEFp(ECG,P1,P2,tab=None,Jcoord=False)

def doubleEFp(ECG,P,Jcoord=False,T1=None):
    '''
    This method returns Q=[2]P
    - ECG is an EC curve group
    - assuming P is an ECpoint of ECG where ECG is an EC over Fp
    - P is in Jacobian coordinate if Jcoord is True and in affine coordinates
    otherwise
    - T1 is a complementary value used to compute [2]P in Jacobian coor-
    dinates, it is equal to Zp2 and is computed if T1 is set to None
    - P is a 3-uple of x-,y-, and z- coordinates if Jcoord is true
    - P is a 3-uple of x-, y- coordinates and a boolean telling if P is
    the point at infinity (in this case x and y could be anything)
    '''

    if Jcoord :
        Xp,Yp,Zp = P
        if Zp == 0 or Yp == 0:
            # P is the point at infinity or P is on the x-axis => [2]P = O
            zero = gmpy.mpz(0)
            Xq,Yq,Zq = zero,gmpy.mpz(1),zero
        else:
            p = ECG.F.char
            if T1==None:
                T1 = Zp**2
            M = 3*Xp**2+(ECG.E.a.val)*(T1**2)
            Yp2 = Yp**2
            T = Yp2**2
            S =  4*Xp*(Yp2)

            Xq = (M**2-2*S)%p
            Yq = (M*(S-Xq)-8*T)%p
            Zq = (2*Yp*Zp)%p
        return Xq,Yq,Zq
    else :
        #Affine coordinates used
        Xp,Yp,Pinf = P
        if Pinf or Yp==0:
            # P is the point at infinity or P is on the x-axis => [2]P = O
            Xq,Yq,Qinf = gmpy.mpz(0),gmpy.mpz(1),True
        else :
            p = ECG.F.char
            l= gmpy.divm(3*Xp**2+ECG.E.a.val,2*Yp,p)

            Xq = (l**2-2*Xp)%p
            Yq = ((Xp-Xq)*l-Yp)%p
            Qinf = False
        return Xq,Yq,Qinf

def daddEFp(ECG,P1,P2, Jcoord=False,tab = None):
    '''
    This method returns Q=P1+P2
    - ECG is an EC curve group
    - assuming P1,P2 are EC points of ECG where ECG is an EC over Fp
    - P1,P2 are in Jacobian coordinate if Jcoord is True and in affine
    coordinates otherwise
    - Tab contains 6 complementary values used to compute Q in Jacobian coor-
    dinates, it is computed if tab is set to None
    - if Jcoord is true, P1,P2 are 3-uple of x-,y-, and z- coordinates
    - if Jcoord is false, P1,P2 are 3-uple of x-, y- coordinates plus a
    boolean Pinf telling if P is the point at infinity
    '''

    if Jcoord:
        Xp1,Yp1,Zp1 = P1
        Xp2,Yp2,Zp2 = P2
        if Zp1 == 0:
            Xq,Yq,Zq = Xp2,Yp2,Zp2
        elif Zp2 == 0:
            Xq,Yq,Zq = Xp1,Yp1,Zp1
        if Xp1 == Xp2 :
            # P1 and P2 have same x coordinate (but not same y) : P1+P2 = O
            zero = gmpy.mpz(0)
            Xq,Yq,Zq = zero,gmpy.mpz(1),zero
        else :
            p = ECG.F.char
            if tab == None :
                T1 = Zp1**2
                T2 = Zp2**2
                A = Xp1*T2 # Xp1*Zp2**2
                B = Xp2*T1 # Xp2*Zp1**2
                C = Yp1*T2*Zp2 # Yp1*Zp2**3
                D = Yp2*T1*Zp1 # Yp2*Zp1**3
            else :
                T1,T2,A,B,C,D = tab
            E = B-A
            F = D-C
            E2 = E**2
            E3 = E2*E
            AE2 = A*E2

            Xq = (F**2-E3-2*AE2)%p
            Yq = (F*(AE2-Xq)-C*E3)%p
            Zq = (Zp1*Zp2*E)%p
        return Xq,Yq,Zq
    else :
        Xp1,Yp1,P1inf = P1
        Xp2,Yp2,P2inf = P2
        if Xp1 == Xp2 :
            Xq,Yq,Qinf = gmpy.mpz(0),gmpy.mpz(1),True
        else :
            p = ECG.F.char
            l = gmpy.divm(Yp2-Yp1,Xp2-Xp1,p)

            Xq = (l**2-Xp1-Xp2)%p
            Yq = ((Xp1-Xq)*l-Yp1)%p
            Qinf = False

        return Xq,Yq,Qinf

def prec_comb2_EFp(w,m,P,Jcoord):
    ''' This method returns a precomputed table of values used to computed fast
    scalar multiplication of P using comb2 see [1]
    - assuming P is an EC point of ECG where ECG is EFp
    - w is the length of the windows
    - m is the bit lenght of alpha
    - the precomputed table stores point in Jacobian coordinates if Jcoord is true
    and in affine coordinates otherwise
    '''
    ECG = P.ECG
    def mul(P,alpha):
        return mulECP(ECG,P,alpha,False, Jcoord)
    def add(P1,P2):
        return addEFp(ECG,P1,P2,Jcoord)
    Pt = toTupleEFp(P,Jcoord)
    return precomp_comb2(w,m,Pt,add,mul)

def mul_comb2_EFp(ECG,alpha,tab,Jcoord):
    ''' This method returns [alpha]P where P is a EC Point of EFp the ECG
    - assuming precomputed values of P are stored in tab as well as other parameters
    to be used in the comb2 method
    - the method returns a tuple in Jcoord if Jcoord is true and in affine otherwise
    '''
    def add(P1,P2):
        return addEFp(ECG,P1,P2, Jcoord)
    def dble(P):
        return doubleEFp(ECG,P,Jcoord)
    def inf(P):
        if Jcoord :
            return P[2] == 0
        else :
            return P[2] == True
    if alpha<0:
        Xp,Yp,Zp = mul_comb2(-alpha,tab,add,dble,inf)
        return Xp,-Yp,Zp
    else :
        return mul_comb2(alpha,tab,add,dble,inf)

def toEFp(ECG,P,Jcoord=False):
    ''' P is a 3-uple (Xp,Yp,Zp) in Fp or P is (Xp,Yp,Pinf)
    return a point in EFp with these coordinates
    assuming self is EFp
    '''
    if Jcoord:
        Xp,Yp,Zp = P
        if Zp == 0 :
            return ECG.infty
        else :
            Fp = ECG.F
            X = field.FieldElem(Xp,Fp)
            Y = field.FieldElem(Yp,Fp)
            Z = field.FieldElem(Zp,Fp)
            Q = ellipticCurve.ECPoint(X,Y,Z,ECG,infty=False,Jcoord=Jcoord)
            assert Q.isOnCurve()
            return Q
            #return ECG.elem(Xp,Yp,Zp,True)
    else:
        Xp,Yp,Pinf = P
        if Pinf :
            return ECG.infty
        else:
            Fp = ECG.F
            X = field.FieldElem(Xp,Fp)
            Y = field.FieldElem(Yp,Fp)
            Q = ellipticCurve.ECPoint(X,Y,1,ECG,Pinf,Jcoord)
            assert Q.isOnCurve()
            return Q
            #return ECG.elem(Xp,Yp)

def toTupleEFp(P,Jcoord=False):
    ''' Return a 3-uple of gmpy.mpz x,y,z or x,y, infty if Jcoord is False
    assuming P belongs to EFp (ECGroup over Fp)
    '''
    if Jcoord :
        if P.infty :
            return gmpy.mpz(0),gmpy.mpz(1),gmpy.mpz(0)
        elif not P.Jcoord :
            return P.x.val,P.y.val,gmpy.mpz(1)
        else :
            return P.x.val,P.y.val,P.z.val
    else :
        if P.infty:
            return gmpy.mpz(0), gmpy.mpz(0), True
        elif P.Jcoord :
            P.toAffine()
            return toTupleEFp(P,False)
        else :
            return P.x.val,P.y.val,P.infty


########################################################################
################# Curve over Fp2 #######################################
########################################################################

def conj(x):
    ''' assuming x is an element of Fp2
    returns the conjugate of x
    '''
    Xc = x.poly.coef
    Xp = field.polynom(x.F.F,[-Xc[0],Xc[1]])
    return field.ExtensionFieldElem(x.F,Xp)

#### Operations over tuples ####

def sqr2(a0,a1):
    return a0**2-a1**2,2*a0*a1
def mul2(a0,a1,b0,b1):
    return a0*b0-a1*b1,a0*b1+a1*b0
def invert2(a0,a1,p):
    c = gmpy.invert(a0**2+a1**2,p)
    return a0*c,-a1*c
def conj2(a0,a1):
    return a0,-a1
def mulconj2(a0,a1,b0,b1,p):
    ''' product of conj(a) times b in Fp2
    a,b are 2-uple in Fp
    returns a 2-uple in Fp
    '''
    return (a0*b0+a1*b1)%p,(a0*b1-a1*b0)%p

def addEFp2(ECG,P1,P2,Jcoord=False):
    ''' This method returns
        - if Jcoord is True : a 6-uple P3x0,P3x1,P3y0,P3y1,P3z0,P3z1 = P3 = P1+P2

        -  if not : a 5-uple Xp30,Xp31,Yp30,Yp31,P3inf where P3 = (Xp30,Xp31,Yp30,Yp31)
            and P3inf is a boolean
        assuming P1,P2 are 6-uple (or 5-uple) of values in Fp
        assuming ECG.F = Fp2 (is the complex field)
    '''
    if Jcoord :
        Xp10,Xp11,Yp10,Yp11,Zp10,Zp11 = P1
        Xp20,Xp21,Yp20,Yp21,Zp20,Zp21 = P2
        if Zp10 == 0 and Zp11 == 0:
            return Xp20,Xp21,Yp20,Yp21,Zp20,Zp21
        elif Zp20 == 0 and Zp21 == 0:
            return Xp10,Xp11,Yp10,Yp11,Zp10,Zp11
        else:
            T10,T11 = sqr2(Zp10,Zp11) # T1 = Zp1**2
            T20,T21 = sqr2(Zp20,Zp21) # T2 = Zp2**2
            U10,U11 = mul2(Xp10,Xp11,T20,T21) # U1 = Xp1*T2
            U20,U21 = mul2(Xp20,Xp21,T10,T11) # U2 = Xp2*T1
            k0,k1 = mul2(Yp10,Yp11,T20,T21)
            S10,S11 = mul2(k0,k1,Zp20,Zp21) # S1 = Yp1*T2*Zp2
            l0,l1 = mul2(Yp20,Yp21,T10,T11)
            S20,S21 = mul2(l0,l1,Zp10,Zp11) # S2 = Yp2*T1*Zp1
            if U10 == U20 and U11 == U21 and S10 == S20 and S11 == S21:
                # P1 == P2 (doubling)
                if Yp10 == 0 and Yp11 == 0 :
                    # P1 is on the x-axis => [2]P1 = O
                    zero,one = gmpy.mpz(0),gmpy.mpz(1)
                    return zero,zero,one,zero,zero,zero
                else:
                    return doubleEFp2(ECG,P1,P2,(T10,T11),Jcoord)
            else :
                #P1 != P2
                if Xp10 == Xp20 and Xp11 == Xp21 :
                    # P1 and P2 have same x coordinate (but not same y) : P1+P2 = O
                    zero,one = gmpy.mpz(0),gmpy.mpz(1)
                    return zero,zero,one,zero,zero,zero
                else :
                    tab = (U10,U11,U20,U21,S10,S11,S20,S21)
                    return daddEFp2(ECG,P1,P2,tab,Jcoord)
    else:
        #Affine coordinates
        Xp10,Xp11,Yp10,Yp11,P1inf = P1
        Xp20,Xp21,Yp20,Yp21,P2inf = P2
        if P1inf:
            return Xp20,Xp21,Yp20,Yp21,P2inf
        elif P2inf:
            return Xp10,Xp11,Yp10,Yp11,P1inf
        elif P1==P2:
            # P1 == P2 (doubling)
            if Yp10 == 0 and Yp11 == 0 :
                # P1 is on the x-axis => [2]P1 = O
                zero,one = gmpy.mpz(0),gmpy.mpz(1)
                return zero,zero,one,zero,True
            else :
                return doubleEFp2(ECG,P1,Jcoord=Jcoord)
        else :
            #P1!=P2
            if Xp10 == Xp20 and Xp11 == Xp21 :
                # P1 and P2 have same x coordinate (but not same y) : P1+P2 = O
                zero,one = gmpy.mpz(0),gmpy.mpz(1)
                return zero,zero,one,zero,True
            else :
                return daddEFp2(ECG,P1,P2,Jcoord=Jcoord)

def daddEFp2(ECG,P1,P2,tab=None,Jcoord=False):
    '''
	This method returns Q=P1+P2
	- ECG is an EC curve group
	- assuming P1,P2 are EC points of ECG where ECG is an EC over Fp2
	- P1,P2 are in Jacobian coordinate if Jcoord is True and in affine
	coordinates otherwise
	- Tab contains 8 complementary values used to compute Q in Jacobian coor-
	dinates, it is computed if tab is set to None
	- if Jcoord is true, P1,P2 are 6-uple of x-,y-, and z- coordinates
	- if Jcoord is false, P1,P2 are 5-uple of x-, y- coordinates plus a
	boolean Pinf telling if P is the point at infinity
	'''
    #Notations
    p = ECG.F.char

    if Jcoord :
        Xp10,Xp11,Yp10,Yp11,Zp10,Zp11 = P1
        Xp20,Xp21,Yp20,Yp21,Zp20,Zp21 = P2
        if Zp10 == 0 and Zp11 == 0:
            Xq0,Xq1,Yq0,Yq1,Zq0,Zq1 = Xp20,Xp21,Yp20,Yp21,Zp20,Zp21
        elif Zp20 == 0 and Zp21 == 0:
            Xq0,Xq1,Yq0,Yq1,Zq0,Zq1 = Xp10,Xp11,Yp10,Yp11,Zp10,Zp11
        elif Xp10 == Xp20 and Xp11 == Xp21 :
            # P1 and P2 have same x coordinate (but not same y) : P1+P2 = O
            zero,one = gmpy.mpz(0),gmpy.mpz(1)
            Xq0,Xq1 = zero,zero
            Yq0,Yq1 = one,zero
            Zq0,Zq1 = zero,zero
        else:
            if tab == None :
                T10,T11 = sqr2(Zp10,Zp11) # T1 = Zp1**2
                T20,T21 = sqr2(Zp20,Zp21) # T2 = Zp2**2
                U10,U11 = mul2(Xp10,Xp11,T20,T21) # U1 = Xp1*T2
                U20,U21 = mul2(Xp20,Xp21,T10,T11) # U2 = Xp2*T1
                k0,k1 = mul2(Yp10,Yp11,T20,T21)
                S10,S11 = mul2(k0,k1,Zp20,Zp21) # S1 = Yp1*T2*Zp2
                l0,l1 = mul2(Yp20,Yp21,T10,T11)
                S20,S21 = mul2(l0,l1,Zp10,Zp11) # S2 = Yp2*T1*Zp1
            else :
                U10,U11,U20,U21,S10,S11,S20,S21 = tab

            H0,H1 = U10-U20,U11-U21 # H = U1-U2
            m0,m1 = sqr2(H0,H1)
            G0,G1 = mul2(m0,m1,H0,H1) # G = H**3
            R0,R1 = S10-S20,S11-S21 # R = S1-S2
            V0,V1 = mul2(U10,U11,m0,m1) # V = U1*(H**2)
            n0,n1 = sqr2(R0,R1)

            Xq0,Xq1 = (n0+G0-2*V0)%p,(n1+G1-2*V1)%p # Xq = (R**2+G-2*V)%p
            o0,o1 = mul2(R0,R1,V0-Xq0,V1-Xq1)
            p0,p1 = mul2(S10,S11,G0,G1)
            Yp30,Yp31 = (o0-p0)%p,(o1-p1)%p # Yq = (R*(V-Xq)-S1*G)%p
            q0,q1 = mul2(Zp10,Zp11,Zp20,Zp21)
            r0,r1 = mul2(q0,q1,H0,H1)
            Zq0,Zq1 = r0%p,r1%p # Zq = (Zp1*Zp2*H)%p

        return Xq0,Xq1,Yq0,Yq1,Zq0,Zq1
    else :
        # Affine coordinates
        Xp10,Xp11,Yp10,Yp11,P1inf = P1
        Xp20,Xp21,Yp20,Yp21,P2inf = P2
        if P1inf:
            Xq0,Xq1,Yq0,Yq1,Qinf = Xp20,Xp21,Yp20,Yp21,P2inf
        elif P2inf:
            Xq0,Xq1,Yq0,Yq1,Qinf = Xp10,Xp11,Yp10,Yp11,P1inf
        elif Xp10 == Xp20 and Xp11 == Xp21 :
            # P1 and P2 have same x coordinate (but not same y) : P1+P2 = O
            zero,one = gmpy.mpz(0),gmpy.mpz(1)
            Xq0,Xq1 = zero,zero
            Yq0,Yq1 = one,zero
            Qinf = True
        else :
            r0,r1 = invert2(Xp20-Xp10,Xp21-Xp11,p)
            #l = gmpy.divm(Yp2-Yp1,Xp2-Xp1,p)
            l0,l1 = mul2(Yp20-Yp10,Yp21-Yp11,r0,r1)
            s0,s1 = sqr2(l0,l1)

            Xq0,Xq1 = (s0-Xp10-Xp20)%p,(s1-Xp11-Xp21)%p #Xq = (l**2-Xp1-Xp2)%p
            q0,q1 = mul2(Xp10-Xq0,Xp11-Xq1,l0,l1)
            Yq0,Yq1 = (q0-Yp10)%p,(q1-Yp11)%p #Yq = ((Xp1-Xq)*l-Yp1)%p
            Qinf = False

        return Xq0,Xq1,Yq0,Yq1,Qinf

def doubleEFp2(ECG,P,tab=None,Jcoord=False):
    '''
	This method returns Q=[2]P
	- ECG is an EC curve
	- assuming P is an ECpoint of ECG where ECG is an EC over Fp2
	- P is in Jacobian coordinate if Jcoord is True and in affine coordinates
	otherwise
	- tab contains 2 complementary values used to compute [2]P in Jacobian coor-
	dinates, it is computed if tab is set to None
	- P is a 6-uple of x-,y-, and z- coordinates if Jcoord is true
	- P is a 5-uple of x-, y- coordinates and a boolean telling if P is
	the point at infinity (in this case x and y could be anything)
	'''
    # Notations
    p = ECG.F.char
    E = ECG.E
    a0 = E.a.poly.coef[1].val
    a1 = E.a.poly.coef[0].val

    def sqr2(a0,a1):
        return a0**2-a1**2,2*a0*a1
    def mul2(a0,a1,b0,b1):
        return a0*b0-a1*b1,a0*b1+a1*b0
    def invert2(a0,a1,p):
        c = gmpy.invert(a0**2+a1**2,p)
        return a0*c,-a1*c

    if Jcoord :
        Xp0,Xp1,Yp0,Yp1,Zp0,Zp1 = P
        if (Zp0 == 0 and Zp1 == 0) or (Yp0 == 0 and Yp1 == 0):
            # P is the point at infinity or P is on the x-axis => [2]P1 = O
            zero,one = gmpy.mpz(0),gmpy.mpz(1)
            Xq0,Xq1 = zero,zero
            Yq0,Yq1 = one,zero
            Zq0,Zq1 = zero,zero
        else:
            if tab == None :
                # T = Zp**2
                T0,T1 = sqr2(Zp0,Zp1)
            else :
                T0,T1 = tab

            R0,R1 = sqr2(Xp0,Xp1) # R = Xp**2
            V0,V1 = sqr2(T0,T1) # V = Zp**4
            W0,W1 = mul2(a0,a1,V0,V1) # W = aZp**4
            M0,M1 = 3*R0+W0,3*R1+W1 # M = 3*Xp**2+a*Zp**4
            O0,O1 = sqr2(Yp0,Yp1) # O = Yp**2
            U0,U1 = sqr2(O0,O1) # U = Yp**4
            N0,N1 = mul2(Xp0,Xp1,O0,O1) # N =  Xp*Yp**2
            S0,S1 = 4*N0,4*N1 # S =  4*Xp*Yp1**2
            M20,M21 = sqr2(M0,M1)

            Xq0,Xq1 = (M20-2*S0)%p,(M21-2*S1)%p
            l0,l1 = mul2(M0,M1,S0-Xq0,S1-Xq1)
            Yq0,Yq1 = (l0-8*U0)%p,(l1-8*U1)%p # Yq = (M*(S-Xp3)-8*T)%p
            k0,k1 = mul2(Yp0,Yp1,Zp0,Zp1)
            Zq0,Zq1 = (2*k0)%p,(2*k1)%p

        return Xq0,Xq1,Yq0,Yq1,Zq0,Zq1
    else:
        # Affine coordinates
        Xp0,Xp1,Yp0,Yp1,Pinf = P
        if Pinf or (Yp0 == 0 and Yp1 == 0) :
            # P is the point at infinity or P is on the x-axis => [2]P1 = O
            zero,one = gmpy.mpz(0),gmpy.mpz(1)
            Xq0,Xq1 = zero,zero
            Yq0,Yq1 = one,zero
            Qinf = True
        else :
            S0,S1 = sqr2(Xp0,Xp1) # S = Xp**2
            t0,t1 = 3*S0+a0,3*S1+a1
            u0,u1 = invert2(2*Yp0,2*Yp1,p)
            l0,l1 = mul2(t0,t1,u0,u1)
            k0,k1 = sqr2(l0,l1)

            Xq0,Xq1 = (k0-2*Xp0)%p,(k1-2*Xp1)%p # Xq = (l**2-2*Xp)%p
            j0,j1 = Xp0-Xq0,Xp1-Xq1
            m0,m1 = mul2(j0,j1,l0,l1)
            Yq0,Yq1 = (m0-Yp0)%p,(m1-Yp1)%p # Yq = ((Xp-Xq)*l-Yp)%p
            Qinf = False

        return Xq0,Xq1,Yq0,Yq1,Qinf

def prec_comb2_EFp2(w,m,P,Jcoord):
    ''' This method returns a precomputed table of values used to computed fast
    scalar multiplication of P using comb2 see [1]
    - assuming P is an EC point of ECG where ECG is EFp2
    - w is the length of the windows
    - m is the bit lenght of alpha
    - the precomputed table stores point in Jacobian coordinates if Jcoord is true
    and in affine coordinates otherwise
    '''
    ECG = P.ECG
    def add(P1,P2):
        return addEFp2(ECG,P1,P2,Jcoord)
    def mul(P,alpha):
        return mulECP(ECG,P,alpha,True,Jcoord)
    Pt = toTupleEFp2(P,Jcoord)
    return precomp_comb2(w,m,Pt,add,mul)

def mul_comb2_EFp2(ECG,alpha,tab,Jcoord):
    ''' This method returns [alpha]P where P is an EC Point of EFp2, the ECG
    - assuming precomputed values of P are stored in tab as well as other parameters
    to be used in the comb2 method
    - the method returns a tuple in Jcoord if Jcoord is true and in affine otherwise
    '''
    def dadd(P1,P2):
        return daddEFp2(ECG,P1,P2, Jcoord)
    def dble(P):
        return doubleEFp2(ECG,P,Jcoord)
    def inf(P):
        if Jcoord :
            return (P[4] == 0) and (P[5] == 0)
        else :
            return P[4] == True
    if alpha<0 :
        if Jcoord :
            Xp0,Xp1,Yp0,Yp1,Zp0,Zp1 = mul_comb2(-alpha,tab,dadd,dble,inf)
            return  Xp0,Xp1,-Yp0,-Yp1,Zp0,Zp1
        else :
            Xp0,Xp1,Yp0,Yp1,Pinf = mul_comb2(-alpha,tab,dadd,dble,inf)
            return  Xp0,Xp1,-Yp0,-Yp1,Pinf
    else :
        return mul_comb2(alpha,tab,dadd,dble,inf)

def toEFp2(ECG,Q,Jcoord=False):
    ''' Q is a 6-uple (Xq0,Xq1,Yq0,Yq1,Zq0,Zq1) in Fp
    or Q is a 5-uple (Xq0,Xq1,Yq0,Yq1,Qinf)
    return a point in EFp2 with these coordinates (Xq = Xq0+Xq1*A ; ...)
    assuming ECG is EFp2
    '''

    # Notations
    F2 = ECG.F
    F = F2.F

    if Jcoord :
        Xq0,Xq1,Yq0,Yq1,Zq0,Zq1 = Q
        if Zq0 == 0 and Zq1 == 0:
            return ECG.infty
        else :
            Xq0e = field.FieldElem(Xq0,F)
            Xq1e = field.FieldElem(Xq1,F)
            Xqp = field.polynom(F,[Xq1e,Xq0e])
            Xq = field.ExtensionFieldElem(F2,Xqp)
            Yq0e = field.FieldElem(Yq0,F)
            Yq1e = field.FieldElem(Yq1,F)
            Yqp = field.polynom(F,[Yq1e,Yq0e])
            Yq = field.ExtensionFieldElem(F2,Yqp)
            Zq0e = field.FieldElem(Zq0,F)
            Zq1e = field.FieldElem(Zq1,F)
            Zqp = field.polynom(F,[Zq1e,Zq0e])
            Zq = field.ExtensionFieldElem(F2,Zqp)
            P = ellipticCurve.ECPoint(Xq,Yq,Zq,ECG,infty=False,Jcoord=Jcoord)
            assert P.isOnCurve()
            return P
            #return self.elem(Xq,Yq,Zq,True)
    else :
        Xq0,Xq1,Yq0,Yq1,Qinf = Q
        if Qinf :
            return ECG.infty
        else :
            F2 = ECG.F
            F = F2.F

            Xq0e = field.FieldElem(Xq0,F)
            Xq1e = field.FieldElem(Xq1,F)
            Xqp = field.polynom(F,[Xq1e,Xq0e])
            Xq = field.ExtensionFieldElem(F2,Xqp)
            Yq0e = field.FieldElem(Yq0,F)
            Yq1e = field.FieldElem(Yq1,F)
            Yqp = field.polynom(F,[Yq1e,Yq0e])
            Yq = field.ExtensionFieldElem(F2,Yqp)
            P = ellipticCurve.ECPoint(Xq,Yq,1,ECG,infty=False,Jcoord=Jcoord)
            assert P.isOnCurve()
            return P
            #return self.elem(Xq,Yq)

def toTupleEFp2(P,Jcoord=False):
    ''' Return a 6-uple of gmpy.mpz x0,x1,y0,y1,z0,z1 i Jcoord is True
    or a 5-uple x0,x1,y0,y1,inf if Jcoord is False
    as Q.x = x0+x1*A, Q.y = y0+y1*A and Q.z = z0+z1*A
    assuming P belongs to EFp2 (ECGroup over Fp2 (complex Field))
    '''
    if Jcoord :
        if P.infty :
            zero = gmpy.mpz(0)
            x0,x1 = zero,zero
            y0,y1 = zero,gmpy.mpz(1)
            z0,z1 = zero,zero
        elif not P.Jcoord :
            x0,x1 = P.x.poly.coef[1].val,P.x.poly.coef[0].val
            y0,y1 = P.y.poly.coef[1].val,P.y.poly.coef[0].val
            z0,z1 = gmpy.mpz(1), gmpy.mpz(0)
        else :
            x0,x1 = P.x.poly.coef[1].val,P.x.poly.coef[0].val
            y0,y1 = P.y.poly.coef[1].val,P.y.poly.coef[0].val
            z0,z1 = P.z.poly.coef[1].val,P.z.poly.coef[0].val
        return x0,x1,y0,y1,z0,z1
    else:
        if P.infty :
            zero = gmpy.mpz(0)
            x0,x1 = zero,zero
            y0,y1 = zero,gmpy.mpz(1)
            Qinf = True
        elif P.Jcoord :
            P.toAffine()
            return toTupleEFp2(P,False)
        else :
            x0,x1 = P.x.poly.coef[1].val,P.x.poly.coef[0].val
            y0,y1 = P.y.poly.coef[1].val,P.y.poly.coef[0].val
            Qinf = False
        return x0,x1,y0,y1,Qinf


########################################################################
################# Operations in Fp**12 #################################
########################################################################

def mulFp12(Fpk,a,b,tab=None):
    ''' Assuming a,b are in Fpk, that is Fp12
    Return the product of a,b by performing operations exclusively in Fp2
    '''
    Fp6 = Fpk.F
    Fp2 = Fp6.F
    xi = -Fp6.irpoly.coef[-1]
    A0,A1 = a.poly.coef
    a5,a4,a3 = A0.poly.coef
    a2,a1,a0 = A1.poly.coef
    B0,B1 = b.poly.coef
    b5,b4,b3 = B0.poly.coef
    b2,b1,b0 = B1.poly.coef
    c5 = a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0
    c4 = a0*b4+a1*b3+xi*(a2*b5+a5*b2)+a3*b1+a4*b0
    c3 = a0*b3+xi*(a1*b5+a2*b4+a4*b2+a5*b1)+a3*b0
    c2 = a0*b2+a1*b1+a2*b0+xi*(a3*b5+a4*b4+a5*b3)
    c1 = a0*b1+a1*b0+xi*(a2*b2+a3*b4+a4*b3+xi*a5*b5)
    c0 = a0*b0+xi*(a1*b2+a2*b1+a3*b3+xi*(a4*b5+a5*b4))
    lp0 = field.polynom(Fp2,[c2,c1,c0])
    lp1 = field.polynom(Fp2,[c5,c4,c3])
    le0 = field.ExtensionFieldElem(Fp6,lp0)
    le1 = field.ExtensionFieldElem(Fp6,lp1)
    lp = field.polynom(Fp6,[le1,le0])
    l = field.ExtensionFieldElem(Fpk,lp)
    return l

def tmulFp12(Fpk,a,b,gamma):
    ''' Return the product c = a*b % p in Fpk, that is Fp12
    where a,b,c are 12-uple of gmpy.mpz
    operations are done only in Fp
    - the method returns a 12-uple of values in Fp forming an element of Fp12
    '''
    p = Fpk.char
    g1,g2,g3,g4 = gamma[10:14]
    a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11 = a
    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11 = b

    c0 = (a0*b0-a1*b1+a2*(g1*b4-g2*b5)-a3*(g2*b4+g1*b5)+a4*(g1*b2-g2*b3)-a5*(g2*b2+g1*b3)+ a6*(g1*b6-g2*b7)-a7*(g2*b6+g1*b7)+a8*(g3*b10-g4*b11)-a9*(g4*b10+g3*b11)+ a10*(g3*b8-g4*b9)-a11*(g4*b8+g3*b9))%p
    #
    c1 = (a0*b1+a1*b0+a2*(g1*b5+g2*b4)+a3*(g1*b4-g2*b5)+a4*(g2*b2+g1*b3)+a5*(g1*b2-g2*b3)+a6*(g2*b6+g1*b7)+a7*(g1*b6-g2*b7) +a8*(g4*b10+g3*b11)+ a9*(g3*b10-g4*b11)+ a10*(g4*b8+g3*b9)+a11*(g3*b8-g4*b9))%p
    #
    c2 = (a0*b2-a1*b3+a2*b0-a3*b1+a4*(g1*b4-g2*b5)-a5*(g2*b4+g1*b5)+a6*(g1*b8-g2*b9)- a7*(g2*b8+g1*b9)+ a8*(g1*b6-g2*b7)-a9*(g2*b6+g1*b7)+ a10*(g3*b10-g4*b11)-a11*(g4*b10+g3*b11))%p
    #
    c3 = (a0*b3+a1*b2+a2*b1+a3*b0+a4*(g2*b4+g1*b5)+a5*(g1*b4-g2*b5)+ a6*(g2*b8+g1*b9)+ a7*(g1*b8-g2*b9)+ a8*(g2*b6+g1*b7)+a9*(g1*b6-g2*b7)+a10*(g4*b10+g3*b11)+a11*(g3*b10-g4*b11))%p
    #
    c4 = (a0*b4-a1*b5+a2*b2-a3*b3+a4*b0-a5*b1+a6*(g1*b10-g2*b11)-a7*(g2*b10+g1*b11)+ a8*(g1*b8-g2*b9)- a9*(g2*b8+g1*b9)+a10*(g1*b6-g2*b7)-a11*(g2*b6+g1*b7))%p
    #
    c5 = (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*(g2*b10+g1*b11)+a7*(g1*b10-g2*b11)+ a8*(g2*b8+g1*b9)+ a9*(g1*b8-g2*b9)+a10*(g2*b6+g1*b7)+a11*(g1*b6-g2*b7))%p
    #
    c6 = (a0*b6-a1*b7+a2*(g1*b10-g2*b11)-a3*(g2*b10+g1*b11)+a4*(g1*b8-g2*b9)-a5*(g2*b8+g1*b9)+ a6*b0-a7*b1+a8*(g1*b4-g2*b5)-a9*(g2*b4+g1*b5)+a10*(g1*b2-g2*b3)-a11*(g2*b2+g1*b3))%p
    #
    c7 = (a0*b7+a1*b6+a2*(g1*b11+g2*b10)+a3*(g1*b10-g2*b11)+a4*(g2*b8+g1*b9)+a5*(g1*b8-g2*b9)+ a6*b1+a7*b0+a8*(g2*b4+g1*b5)+a9*(g1*b4-g2*b5)+a10*(g2*b2+g1*b3)+a11*(g1*b2-g2*b3))%p
    #
    c8 = (a0*b8-a1*b9+a2*b6-a3*b7+a4*(g1*b10-g2*b11)-a5*(g2*b10+g1*b11)+a6*b2-a7*b3+a8*b0-a9*b1+a10*(g1*b4-g2*b5)-a11*(g2*b4+g1*b5))%p
    #
    c9 = (a0*b9+a1*b8+a2*b7+a3*b6+a4*(g2*b10+g1*b11)+a5*(g1*b10-g2*b11)+ a6*b3+ a7*b2+ a8*b1+ a9*b0+a10*(g2*b4+g1*b5)+a11*(g1*b4-g2*b5))%p
    #
    c10 = (a0*b10-a1*b11+a2*b8-a3*b9+a4*b6-a5*b7+a6*b4-a7*b5+a8*b2-a9*b3+a10*b0-a11*b1)%p
    #
    c11 = (a0*b11+a1*b10+a2*b9+a3*b8+a4*b7+a5*b6+a6*b5+a7*b4+a8*b3+a9*b2+a10*b1+a11*b0)%p

    return c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11

def sqrtFp12(Fpk,a,tab=None):
    ''' Assuming a is in Fpk, that is Fp12
    Return the square of a by performing operations exclusively in Fp2
    '''
    Fp6 = Fpk.F
    Fp2 = Fp6.F
    xi = -Fp6.irpoly.coef[-1]
    A0,A1 = a.poly.coef
    a5,a4,a3 = A0.poly.coef
    a2,a1,a0 = A1.poly.coef

    c5 = 2*(a0*a5+a1*a4+a2*a3)
    c4 = 2*(a0*a4+a1*a3+xi*a2*a5)
    c3 = 2*(a0*a3+xi*(a1*a5+a2*a4))
    c2 = 2*(a0*a2)+Fp2.square(a1)+xi*(2*a3*a5+Fp2.square(a4))
    c1 = 2*(a0*a1)+xi*(Fp2.square(a2)+2*(a3*a4)+xi*Fp2.square(a5))
    c0 = Fp2.square(a0)+xi*(2*(a1*a2)+Fp2.square(a3)+2*xi*(a4*a5))
    lp0 = field.polynom(Fp2,[c2,c1,c0])
    lp1 = field.polynom(Fp2,[c5,c4,c3])
    le0 = field.ExtensionFieldElem(Fp6,lp0)
    le1 = field.ExtensionFieldElem(Fp6,lp1)
    lp = field.polynom(Fp6,[le1,le0])
    l = field.ExtensionFieldElem(Fpk,lp)
    return l

def tsqrtFp12(Fpk,a,gamma):
    ''' Return the squaring c = a**2 % p
    where a,c are 12-uple of gmpy.mpz, a is an element of Fp12
    '''
    p = Fpk.char
    g1,g2,g3,g4 = gamma[10:14]
    a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11 = a

    a00,a01,a02,a03,a04,a05,a06,a07,a08,a09,a010,a011 = a0**2, a0*a1, a0*a2, a0*a3, a0*a4, a0*a5, a0*a6, a0*a7, a0*a8, a0*a9, a0*a10, a0*a11
    #
    a0101,a12,a13,a14,a15,a16,a17,a18,a19,a110,a111 = a1**2,  a1*a2, a1*a3, a1*a4, a1*a5, a1*a6, a1*a7, a1*a8, a1*a9, a1*a10, a1*a11
    #
    a22,a23,a24,a25,a26,a27,a28,a29,a210,a211 = a2**2, a2*a3, a2*a4, a2*a5, a2*a6, a2*a7, a2*a8, a2*a9, a2*a10, a2*a11
    #
    a33,a34,a35,a36,a37,a38,a39,a310,a311 = a3**2, a3*a4, a3*a5, a3*a6, a3*a7, a3*a8, a3*a9, a3*a10, a3*a11
    #
    a44,a45,a46,a47,a48,a49,a410,a411 = a4**2,a4*a5,a4*a6,a4*a7,a4*a8,a4*a9,a4*a10,a4*a11
    #
    a55,a56,a57,a58,a59,a510,a511 = a5**2,a5*a6,a5*a7,a5*a8,a5*a9,a5*a10,a5*a11
    #
    a66,a67,a68,a69,a610,a611 = a6**2,a6*a7,a6*a8,a6*a9,a6*a10,a6*a11
    #
    a77,a78,a79,a710,a711 = a7**2, a7*a8,a7*a9,a7*a10,a7*a11
    #
    a88,a89,a810,a811 = a8**2,a8*a9,a8*a10,a8*a11
    #
    a99,a910,a911 = a9**2,a9*a10,a9*a11
    #
    a1010,a1011 = a10**2,a10*a11
    #
    a1111 = a11**2

    c0 = (a00-a0101+g1*(a66-a77+2*(a24-a35-2*g2*(a910+a811)))-2*(g2*(a25+a34+a67)+g3*(a911-a810)))%p
    #
    c1 = (2*(a01+g1*(a25+a34+a67+2*g2*(a810-a911)))+g2*(a66-a77+2*(a24-a35))+2*g3*(a811+a910))%p
    #
    c2 = (2*(a02-a13+g1*(a68-a79-2*g2*a1011)-g2*(a45+a69+a78))+g1*(a44-a55)+g3*(a1010-a1111))%p
    #
    c3 = (2*(a03+a12+g1*(a45+a69+a78+g2*(a1010-a1111))+g2*(a68-a79)+g3*a1011)+g2*(a44-a55))%p
    #
    c4 = (2*(a04-a15+g1*(a610-a711)-g2*(a611+a710+a89))+a22-a33+g1*(a88-a99))%p
    #
    c5 = (2*(a05+a14+a23+g1*(a611+a710+a89)+g2*(a610-a711))+g2*(a88-a99))%p
    #
    c6 = (2*(a06-a17+g1*(a210-a311+a48-a59)-g2*(a211+a310+a49+a58)))%p
    #
    c7 = (2*(a07+a16+g1*(a211+a310+a49+a58)+g2*(a210-a311+a48-a59)))%p
    #
    c8 = (2*(a08-a19+a26-a37+g1*(a410-a511)-g2*(a411+a510)))%p
    #
    c9 = (2*(a09+a18+a27+a36+g1*(a411+a510)+g2*(a410-a511)))%p
    #
    c10 = (2*(a010-a111+a28-a39+a46-a57))%p
    #
    c11 = (2*(a011+a110+a29+a38+a47+a56))%p

    return c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11

def prec_gamma(Fpk,u,c,d):
    '''
    This method computes a table storing values that are used to fasten
    operations in Fpk, that is Fp12 towered as explained in the introduction of this
    module. It also stores values used to fasten the execution of the pairings
    build on BN curves. For more details see [3].
    '''

    Fp6 = Fpk.F
    g = [0]*14
    xi = -Fp6.irpoly.coef[-1] # 1*A+4 (c**2+d**3*i)
    p = Fpk.char
    e1 = (p-1)/3
    e2 = (p-1)/2
    # These three values are used to compute a final hard expo in Tate Pairing
    g[0] = xi**e1
    g[1] = (xi**2)**e1
    g[2] = xi**e2

    g[3] = 6*u**2 + 1  # i.e. trace of frobenius
    g[4] = -(36*u**3+18*u**2+12*u-1)
    g[5] = -(36*u**3+30*u**2+18*u+2)
    g[6] = u
    g[7] = psi
    # The following values are used to perform fast operations in Fp12
    # see functions tmulFp12 and tsqrtFp12
    g[8] = c
    g[9] = d
    g[10] = c**2
    g[11] = d**3
    g[12] = c**4-d**6
    g[13] = 2*c**2*d**3
    return g

def frobenius(x,gamma,i=1,recall = False):
    ''' Returns x**(p**i) wher p is the order of Fp,
        x is an element of Fp12
    '''
    assert i>0
    G = x.poly.coef[1]
    g0 = G.poly.coef[2]
    g1 = G.poly.coef[1]
    g2 = G.poly.coef[0]
    H = x.poly.coef[0]
    h0 = H.poly.coef[2]
    h1 = H.poly.coef[1]
    h2 = H.poly.coef[0]
    # x = g0+g1*A+g2*A**2+(h0+h1*A+h2*A**2)*B
    # equivalently (W = B  and B**2 = A)
    # x = g0 + h0*W + g1*W**2 + h1*W**3 + g2*W**4 + h2*W**5

    g0c,g1c,g2c,h0c,h1c,h2c = conj(g0),conj(g1),conj(g2),conj(h0),conj(h1),conj(h2)

    f1 = gamma[0] #xi**e1
    f2 = gamma[1] #(xi**2)**e1 where e1 = (p-1)/3
    f3 = gamma[2] #xi**e2 where e2 = (p-1)/2

    ng0 = g0c
    ng1 = g1c*f1
    ng2 = g2c*f2
    nG = field.polynom(x.F.F.F,[ng2,ng1,ng0])
    nGe = field.ExtensionFieldElem(x.F.F,nG)
    nh0 = h0c*f3
    nh1 = h1c*f3*f1
    nh2 = h2c*f3*f2
    nH = field.polynom(x.F.F.F,[nh2,nh1,nh0])
    nHe = field.ExtensionFieldElem(x.F.F,nH)
    nXp = field.polynom(x.F.F,[nHe,nGe])
    y = field.ExtensionFieldElem(x.F,nXp)

    if i == 1:
        return y
    else :
        if not recall :
            return frobenius(y,i-1)
        else :
            return y,frobenius(y,i-1,recall)

def tfrobenius(Fpk,x,gamma,i=1,recall=False):
    ''' Returns x**(p**i) where p is the char. of Fp, x is an element of Fp12
    if recall is true and i>1, this will return a tuple t of i elements where
    t_i = frob_i(x)
    '''
    g = gamma
    assert i>0
    p = Fpk.char
    x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11 = x

    f10,f11 = g[0].poly.coef[1].val,g[0].poly.coef[0].val # xi**e1 where e1 = (p-1)/3
    f20,f21 = g[1].poly.coef[1].val,g[1].poly.coef[0].val # (xi**2)**e1
    f30,f31 = g[2].poly.coef[1].val,g[2].poly.coef[0].val # xi**e2 where e2 = (p-1)/2

    y0 = x0 % p
    y1 = (-x1) % p
    y2 = (f10*x2+f11*x3) % p
    y3 = (f11*x2-f10*x3) % p
    y4 = (f20*x4+f21*x5) % p
    y5 = (f21*x4-f20*x5) % p
    y6 = (f30*x6+f31*x7) % p
    y7 = (f31*x6-f30*x7) % p
    a1 = f30*x8+f31*x9
    a2 = f30*x9-f31*x8
    y8 = (f10*a1+f11*a2) % p
    y9 = (f11*a1-f10*a2) % p
    b1 = f30*x10+f31*x11
    b2 = f30*x11-f31*x10
    y10 = (f20*b1+f21*b2) % p
    y11 = (f21*b1-f20*b2) % p

    y = y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11

    if i == 1:
        return y
    else :
        if not recall :
            return tfrobenius(Fpk,y,g,i-1)
        else :
            return y,tfrobenius(Fpk,y,g,i-1,recall)

def toTupleFp12(a):
    ''' Takes a in Fp12 and returns a 12-uple of values in Fp
    a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11
    where
    a = a0+a1*i+(a2+a3*i)*Y+(a4+a5*i)*Y**2+(a6+a7*i+(a8+a9*i)*Y+(a10+a11*i)*Y**2)*X
    where i**2 = -1 ; Y**3 = X**2 = xi (see intro)
    '''
    A0,A1 = a.poly.coef
    aa5,aa4,aa3 = A0.poly.coef
    a11,a10 = aa5.poly.coef
    a9,a8 = aa4.poly.coef
    a7,a6 = aa3.poly.coef
    aa2,aa1,aa0 = A1.poly.coef
    a5,a4 = aa2.poly.coef
    a3,a2 = aa1.poly.coef
    a1,a0 = aa0.poly.coef

    return a0.val,a1.val,a2.val,a3.val,a4.val,a5.val,a6.val,a7.val,a8.val,a9.val,a10.val,a11.val

def toFp12elem(Fpk,A):
    ''' Takes a 12-uple A=(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)  and returns a
    Fpk element a where Fpk is Fp12:
    a = a0+a1*i+(a2+a3*i)*Y+(a4+a5*i)*Y**2+(a6+a7*i+(a8+a9*i)*Y+(a10+a11*i)*Y**2)*X
    where i**2 = -1 ; Y**3 = X**2 = xi (see intro)
    '''
    a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11 = A

    Fp6 = Fpk.F
    Fp2 = Fp6.F
    Fp = Fp2.F

    a0e,a1e,a2e,a3e,a4e,a5e,a6e,a7e,a8e,a9e,a10e,a11e = Fp.elem(a0), Fp.elem(a1),Fp.elem(a2),Fp.elem(a3),Fp.elem(a4),Fp.elem(a5),Fp.elem(a6),Fp.elem(a7),Fp.elem(a8),Fp.elem(a9),Fp.elem(a10),Fp.elem(a11)
    #
    a01p,a23p,a45p,a67p,a89p,a1011p = field.polynom(Fp,[a1e,a0e]),field.polynom(Fp,[a3e,a2e]),field.polynom(Fp,[a5e,a4e]),field.polynom(Fp,[a7e,a6e]),field.polynom(Fp,[a9e,a8e]),field.polynom(Fp,[a11e,a10e])
    #
    a01e,a23e,a45e,a67e,a89e,a1011e = field.ExtensionFieldElem(Fp2,a01p), field.ExtensionFieldElem(Fp2,a23p), field.ExtensionFieldElem(Fp2,a45p), field.ExtensionFieldElem(Fp2,a67p), field.ExtensionFieldElem(Fp2,a89p), field.ExtensionFieldElem(Fp2,a1011p)
    #
    c0p,c1p = field.polynom(Fp2,[a45e,a23e,a01e]), field.polynom(Fp2,[a1011e,a89e,a67e])
    #
    c0e,c1e = field.ExtensionFieldElem(Fp6,c0p),field.ExtensionFieldElem(Fp6,c1p)
    #
    cp = field.polynom(Fp6,[c1e,c0e])
    #
    c = field.ExtensionFieldElem(Fpk,cp)

    return c


########################################################################
################# Morphism between EC ##################################
########################################################################


def psi(EFpk,P):
    ''' From an EC Point P of E'[Fp2] return an EC Point over EFpk, that is E[Fp12]
    #TODO : Optimize this method
    '''
    Fpk = EFpk.F
    Fp6 = Fpk.F

    if P.infty:
        return EFpk.infty
    z = Fp6.unit()
    xp = Fp6.elem(P.x)
    x = xp*z
    newx = Fpk.elem(x)
    yp = Fp6.elem(P.y)
    y = Fpk.elem(yp)
    w = Fpk.unit()
    newy = y*w
    return EFpk.elem(newx,newy)



########################################################################
################# Optimized Pairings ###################################
########################################################################

def hardexpo(Fpk,m,gamma,frob,intuple=False):
    ''' return m**((q**4-q**2+1)/r)
    This method assumes that m belongs to Fp12
    where u = gamma[6] is the parameter of q(u)
    gamma is a table of precomputed values to
    compute the frobenius
    Algorithm comes from [Scott et Al, Pairing 2009]
    http://eprint.iacr.org/2008/490.pdf
    '''
    # Notations
    g = gamma
    u = g[6]
    mul = mulFp12
    sqrt = sqrtFp12
    sqmu = squareAndMultiply
    if intuple :
        mul = tmulFp12
        sqrt = tsqrtFp12
        mt = toFp12elem(Fpk,m)
        invmt = Fpk.invert(mt) # 1/m #TODO: write a complete inverting method for Fp12 tuple
        invm = toTupleFp12(invmt)
    else :
        mul = mulFp12
        sqrt = sqrtFp12
        invm = Fpk.invert(mt)
    if u<0:
        m1 = sqmu(Fpk,invm,-u,mul,sqrt,g) # 1/(m**(-u)) = m**u
        invm1 = sqmu(Fpk,m,-u,mul,sqrt,g) # m**(-u) = 1/m**u
        m2 = sqmu(Fpk,invm1,-u,mul,sqrt,g) # m**(u**2)
        invm2 = sqmu(Fpk,m1,-u,mul,sqrt,g) #1/m**(u**2)
        invm3 = sqmu(Fpk,m2,-u,mul,sqrt,g) # 1/m**(u**3) = m**(-u**3)
    else :
        m1 = sqmu(Fpk,m,u,mul,sqrt,g) # m**u
        invm1 = sqmu(Fpk,invm,u,mul,sqrt,g) # 1/m**u
        m2 = sqmu(Fpk,m1,u,mul,sqrt,g) # m**(u**2)
        invm2 = sqmu(Fpk,invm1,u,mul,sqrt,g) # 1/(m**(u**2))
        invm3 = sqmu(Fpk,invm2,u,mul,sqrt,g)

    fm1,(fm2,fm3) = frob(Fpk,m,g,3,True)

    y0 = mul(Fpk,mul(Fpk,fm1,fm2,g),fm3,g) # (m**p)*(m**(p**2))*(m**(p**3))
    y1 = invm
    y2 = frob(Fpk,m2,g,2) # (m**(u**2))**(p**2)
    y3 = frob(Fpk,invm1,g) # (1/m**u)**p
    y4 = mul(Fpk,invm1,frob(Fpk,invm2,g),g) # (1/m**u)*(1/m**(u**2))**p
    y5 = invm2
    y6 = mul(Fpk,invm3,frob(Fpk,invm3,g),g) # (1/m**(u**3))**(p+1)

    T0 = sqrt(Fpk,y6,g)
    T0 = mul(Fpk,T0,y4,g)
    T0 = mul(Fpk,T0,y5,g)
    T1 = mul(Fpk,y3,y5,g)
    T1 = mul(Fpk,T1,T0,g)
    T0 = mul(Fpk,T0,y2,g)
    T1 = sqrt(Fpk,T1,g)
    T1 = mul(Fpk,T1,T0,g)
    T1 = sqrt(Fpk,T1,g)
    T0 = mul(Fpk,T1,y1,g)
    T1 = mul(Fpk,T1,y0,g)
    T0 = sqrt(Fpk,T0,g)
    T0 = mul(Fpk,T0,T1,g)

    if intuple :
        return toFp12elem(Fpk,T0)
    else :
        return T0

def OptimTatePairing(P,Q,Pair):
    ''' This method evaluates the Tate pairing using Miller's algorithm
    e(P,Q) where P belongs to G1 and Q to G'2
    Remark that the output x has to be raised to the power of
    (p**k-1)/r to belong to the r-torsion group
    where p =  |Fp| and k is the degree of the extension Fpk over Fp
    This method is faster than classic TatePairing provided in pairing.py
    '''
    # Notations
    Fpk = Pair.Fpk
    r = Pair.r
    e = Pair.e
    frob = frobenius
    g = Pair.gamma
    mul = mulFp12
    sqrt = sqrtFp12
    sqmu = squareAndMultiply
    Fp6 = Fpk.F
    Fp2 = Fp6.F
    f02 = Fp2.zero()
    ################### Algos used in the Tate Pairing ############################
    def LptQ2(P,T,Q):
        ''' P,T belongs to E[Fp]
            Q belongs to E'[Fp2]
            return the evaluation of Q on the line through P and T
            !!! This algo assumes that the curve's coefficient a is zero !!!
        '''
        Qx = Q.x
        Qy = Q.y
        c3 = ((T.x-P.x).val)*Qy
        c1 = ((P.y-T.y).val)*Qx
        c0 = Fp2.elem(T.y*P.x-T.x*P.y)
        c2,c4,c5 = f02,f02,f02
        lp0 = field.polynom(Fp2,[c2,c1,c0])
        lp1 = field.polynom(Fp2,[c5,c4,c3])
        le0 = field.ExtensionFieldElem(Fp6,lp0)
        le1 = field.ExtensionFieldElem(Fp6,lp1)
        lp = field.polynom(Fp6,[le1,le0])
        l = field.ExtensionFieldElem(Fpk,lp)
        return l

    def LppQ2(P,Q):
        ''' P belongs to E[Fp]
            Q belongs to E[Fp2]
            return the evaluation of Q on the tangent line through P
            !!! This algo assumes that the curve's coefficient a is zero !!!
        '''
        Qx = Q.x
        Qy = Q.y
        Px2 = P.x**2
        c0 = Fp2.elem(3*Px2*P.x-2*P.y**2)
        c1 = -3*(Px2).val*Qx
        c3 = 2*(P.y).val*Qy
        c2,c4,c5 = f02,f02,f02
        lp0 = field.polynom(Fp2,[c2,c1,c0])
        lp1 = field.polynom(Fp2,[c5,c4,c3])
        le0 = field.ExtensionFieldElem(Fp6,lp0)
        le1 = field.ExtensionFieldElem(Fp6,lp1)
        lp = field.polynom(Fp6,[le1,le0])
        l = field.ExtensionFieldElem(Fpk,lp)
        return l

    ############## Algorithm for the Tate Pairing #################################
    #init
    x = Fpk.one()
    Z = P
    rbin = bin(r)
    t = len(rbin)-1 # r = r_2...r_t where r_i is in {0,1} the bit repr. of r

    #loop
    for i in range(3,t+1):
        TZQ = LppQ2(Z,Q) # computation in Fp and Fp2
        ZZ = Z+Z # in E[Fp]
        x = mul(Fpk,sqrt(Fpk,x),TZQ) # in Fp12
        Z = ZZ
        if rbin[i]=='1':
            LZPQ = LptQ2(Z,P,Q) # computation in Fp and Fp2
            ZP = Z+P # in E[Fp]
            x = mul(Fpk,x,LZPQ) # in Fp12
            Z = ZP

    if frob == None :
        y = sqmu(Fpk,x,e,mul,sqrt,g) # standardizing x to belong to the correct group
    else :
        # here we use the frobenius endomorphism to compute p-th powers
        # we use formulae proposed in [Devegili et al 07]

        xinv = Fpk.invert(x)
        x1 = mul(Fpk,frob(x,g,6),xinv) # x**(p**6-1)
        x2 = mul(Fpk,frob(x1,g,2),x1)  # x1**(p**2+1)

        y = hardexpo(Fpk,x2,g,frob)

    return y

def OptimAtePairing(P,Q,Pair,Jcoord=False):
    '''
    P is an EC point over E[Fp]
    Q is an EC point over E'[Fp2]
    t is the trace of frobenius of the curve E
    The algorithm outputs the Ate Pairing of (P,Qp) where Qp = psi(Q)
    This method is faster than AtePairing2
    '''
    # Notations
    Fpk = Pair.Fpk
    EFp2 = Q.ECG
    p = Fpk.char
    Fpk1 = Pair.Fpk1
    frob = tfrobenius
    g = Pair.gamma
    mul = tmulFp12
    sqrt = tsqrtFp12
    u = g[6]
    zero = gmpy.mpz(0)
    ################### Algos used in the Tate Pairing ############################
    def LttP(P,T):
        ''' P belongs to E[Fp]
            T is a 5-uple representing a point in EFp2
            return the evaluation (in a tuple) of P on the tangent line through T
            !!! This algo assumes that the curve's coefficient a is zero !!!
            #TODO : implement this method in Jcoord
        '''
        g1,g2 = g[10:12]

        Px = P.x.val
        Py = P.y.val

        xt0,xt1,yt0,yt1,Tinf = T

        xt02 = xt0**2
        xt12 = xt1**2
        a0 = 3*xt0*(xt02-3*xt12)
        a1 = 2*(yt1-yt0)*(yt1+yt0)
        a2 = 3*xt1*(3*xt02-xt12)
        a3 = -4*(yt0*yt1)

        c0 = (g1*(a0+a1)-g2*(a2+a3))%p
        c1 = (g1*(a2+a3)+g2*(a0+a1))%p
        c4 = (3*Px*(xt12-xt02))%p
        c5 = (-6*Px*xt0*xt1)%p
        c6 = (2*yt0*Py)%p
        c7 = (2*yt1*Py)%p

        c2,c3,c8,c9,c10,c11 = zero,zero,zero,zero,zero,zero

        return c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11

    def LqtP(P,Q,T):
        ''' P belongs to E[Fp]
            T,Q are 5-uple representing points in EFp2
            return the evaluation of P on the line through T and Q
            !!! This algo assumes that the curve's coefficient a is zero !!!
            #TODO : implement this method in Jcoord
        '''

        Px = P.x.val
        Py = P.y.val
        xt0,xt1,yt0,yt1,Tinf = T
        xq0,xq1,yq0,yq1,Qinf = Q

        c2 = ((xt0-xq0)*Py)%p
        c3 = ((xt1-xq1)*Py)%p
        c6 = ((yq0-yt0)*Px)%p
        c7 = ((yq1-yt1)*Px)%p
        c8 = (xq0*yt0-xq1*yt1-xt0*yq0+xt1*yq1)%p
        c9 = (xq0*yt1+xq1*yt0-xt0*yq1-xt1*yq0)%p

        c0,c1,c4,c5,c10,c11 = zero,zero,zero,zero,zero,zero

        return c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11

    ############## Algorithm for the Ate Pairing ##################################
    # init
    Qt = toTupleEFp2(Q,Jcoord)
    #Qtj = toTupleEFp2(Q,True)
    Tt = Qt
    #Ttj = Qtj

    x = toTupleFp12(Fpk1)
    tbin = bin(abs(6*u+2))
    l = len(tbin)
    # loop
    for i in range(3,l):
        LTT = LttP(P,Tt)
        x = mul(Fpk,sqrt(Fpk,x,g),LTT,g)
        Tt = doubleEFp2(EFp2,Tt,tab=None,Jcoord=Jcoord)
        if tbin[i] == '1':
            LTQ = LqtP(P,Tt,Qt)
            x = mul(Fpk,x,LTQ,g)
            Tt = daddEFp2(EFp2,Tt,Qt,tab=None,Jcoord=Jcoord)

    if u<0:
        #T = -T
        def neg(T):
            Xt0,Xt1,Yt0,Yt1,Tinf = T
            return Xt0,Xt1,-Yt0,-Yt1,Tinf
        Tt = neg(Tt)
        Y = Fpk.invert(toFp12elem(Fpk,x))
        x = toTupleFp12(Y)

    Qx0,Qx1,Qy0,Qy1,Qinf=Qt
    #Qx = Qx0,Qx1
    #Qy = Qy0,Qy1
    g10,g11 = g[0].poly.coef[1].val,g[0].poly.coef[0].val # xi**e1 where e1 = (p-1)/3

    Q1x0,Q1x1 = mulconj2(Qx0,Qx1,g10,g11,p)
    #Q1x = Q1x0,Q1x1

    g20,g21 = g[2].poly.coef[1].val,g[2].poly.coef[0].val # xi**e2 where e2 = (p-1)/2
    Q1y0,Q1y1 = mulconj2(Qy0,Qy1,g20,g21,p)
    #Q1y = Q1y0,Q1y1
    Q1 = Q1x0,Q1x1,Q1y0,Q1y1,False
    Q2x0,Q2x1 = mulconj2(Q1x0,Q1x1,g10,g11,p)
    Q2y0,Q2y1 = mulconj2(Q1y0,Q1y1,g20,g21,p)
    Q2 = Q2x0,Q2x1,-Q2y0,-Q2y1,False

    LTQ1 = LqtP(P,Tt,Q1)
    x = mul(Fpk,x,LTQ1,g)
    Tt = daddEFp2(EFp2,Tt,Q1,None,Jcoord)

    LTQ2 = LqtP(P,Tt,Q2)
    x = mul(Fpk,x,LTQ2,g)

    xinv = Fpk.invert(toFp12elem(Fpk,x))
    x1 = mul(Fpk,frob(Fpk,x,g,6),toTupleFp12(xinv),g) # x**(p**6-1)
    x2 = mul(Fpk,frob(Fpk,x1,g,2),x1,g)  # x1**(p**2+1)
    y = hardexpo(Fpk,x2,g,frob,True)

    return y









