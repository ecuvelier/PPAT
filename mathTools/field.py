# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

from numpy import *
import gmpy
from Crypto.Random.random import randint
import random as rd
import tools.fingexp as fingexp
import tools.utils as utils


class Field(fingexp.FingExp):
    'Class for Field'

    def __init__(self,p):
        '''Defines the modulus p which must be a prime
        '''
        self.F = self
        self.p = gmpy.mpz(p) # prime modulus
        self.char = self.p # characteristic
        self.q = self.p+1 # order+1 #TODO : correct?
        assert gmpy.is_prime(p)
        self.rep = None
        self.g = None
        '''
        g is a random quadratic residue used to compute square roots and it is
        initialized the first time a square root is computed
        '''

        self.to_fingerprint = ["p"]
        self.to_export = {"fingerprint": [],"value": ["p"]}
        super(Field, self).__init__()

    def load(self, data, fingerprints):
        self.p = utils.b64tompz(data["p"])

    def one(self):
        'unit element for multiplication'
        return FieldElem(1, self)

    def zero(self):
        'unit element for addition'
        return FieldElem(0,self)

    def elem(self,x):
        ''' return an element of value x
        '''
        if isinstance(x,FieldElem):
            assert x.F == self
            return x
        m = gmpy.mpz(1)
        assert isinstance(x,int) or isinstance(x, long) or type(x)==type(m)
        return FieldElem(x,self)

    def random(self,low=1,high=None):
        ''' Return a random element of the Field
        '''
        if high == None :
            high = int(self.p-1)
        rand = randint(low,high)
        return self.elem(rand)

    def __eq__(self, other):
        'testing if we are working in the same field'
        try:
            return (self.p == other.p)
        except:
            return False

    def add(self, a, b):
        '''
        field operation: addition mod p
        '''
        return FieldElem((a.val + b.val) % self.p, self)

    def sub(self, a, b):
        '''
        field operation: substraction mod p
        '''
        return FieldElem((a.val - b.val) % self.p, self)

    def neg(self, a):
        '''
        field operation: opposite mod p
        '''
        return FieldElem((self.p - a.val ) % self.p, self)

    def mul(self, a, b):
        '''
        field operation: multiplication of field elements
        '''
        """
        if isinstance(a,FieldElem) and isinstance(b, FieldElem) and not a.F == b.F :
            raise Exception("multiplication between elements of different fields")
        """
        if not isinstance(b,FieldElem) :
            # Multiplication by a scalar
            if b<0:
                return self.smul(-a,-b)
            return self.smul(a,b)
        else:
            return self.pmul(a,b)

    def smul(self,a,b):
        ''' Return a*b where a or b is scalar
        '''
        if not isinstance(b,FieldElem):
            # b is scalar
            #return self.dbleAndAdd(a,a,b)
            return FieldElem((gmpy.mpz(b)*a.val)%(self.p),self)
            #return self.pmul(a,a.F.elem(b))
        else :
            # a is scalar
            #return self.dbleAndAdd(b,b,a)
            return self.smul(b,a)
    def sm(self,b,a):
        ''' Quick multiplication between a field element a and a scalar b
        '''
        return FieldElem((gmpy.mpz(b)*a.val)%(self.p),self)

    def pmul(self,a,b):
        ''' product between two field element in Fp
        '''
        return FieldElem((a.val * b.val) % self.p, self)

    def dbleAndAdd(self,P,Pp,n):
        'return n*P using double and add technique'
        #print "dblaad"
        if n == 0 :
            return self.zero();
        if n == 1 :
            return P
        elif n%2 == 1 :
            Q = self.dbleAndAdd(P,Pp,(n-1)/2)
            return P+Q+Q
        elif n%2 == 0 :
            Q = self.dbleAndAdd(P,Pp,n/2)
            return Q+Q

    def powop(self, a, b):
        'return a**b'
        m = gmpy.mpz(1)
        #self.count = 0
        'exponentiation by a scalar'
        if not isinstance(b, int) and not isinstance(b, long) and not type(b)==type(m):
            raise Exception("Exponentation by a non integer, long or mpz")
        c = b
        if c > self.char-1 or c<0:
            c = b%(self.char-1)
        #elif :
        #    return self.powop(a.invert(),(-c))
        if c == 0 :
            assert not a.val%self.char == 0
            return self.one()
        elif c == 1 :
            return a
        else :
            return self.sqrtAndMultply(a,a, c)
            #return FieldElem(pow(a.val,b,self.char))

    def sqrtAndMultply(self,P,Pp,n):
        'return P**n using square and multiply technique'
        if n == 0 :
            return self.one()
        elif n == 1 :
            return P
        elif n%2 == 1 :
            Q = self.sqrtAndMultply(P,Pp,(n-1)/2)
            return P*self.square(Q)
        elif n%2 == 0 :
            Q = self.sqrtAndMultply(P,Pp,n/2)
            return self.square(Q)

    def square(self,a):
        '''
        This method returns the square of a
        '''
        return FieldElem(pow(a.val,2, self.p), self)

    def invert(self,a):
        assert not (a.val%self.p == 0) # Do not invert zero!
        return FieldElem(gmpy.invert(a.val, self.p), self)

    #def invertible(self,a):
        #return not int(a.invert().val) == 0

    def div(self,a,b):
        assert not (b.val%self.p == 0) # Do not invert zero!
        return FieldElem((a.val*self.invert(b).val % self.p),self)

    def findnonresidue(self):
        '''
        find a random non quadratic residue in the Field F,
        that is, find g that is not a square in F, this is
        needed to compute square roots
        '''
        g=self.random()
        while g.isquadres():
            #print g, " is quad res in ", self
            g = self.random()
        return g

    def __str__(self):
        return "F_"+str(self.p)

    def jsonable(self):
        return {'type': 'FqField', 'p': self.p}


class FieldElem():
    def __init__(self, val, F):
        '''Creating a new field element.
        '''
        #assert isinstance(F,Field)
        self.F = F
        self.val = gmpy.mpz(val)
        self.poly = polynom(self.F,[self])

        #self.to_fingerprint = ["F", "val"]
        #self.to_export = {"fingerprint": ["F"],
        #                  "value": ["val"]}
        #super(FieldElem, self).__init__()

    def __eq__(self, other):
        try:
            return ((self.val%self.F.char) == (other.val%self.F.char) and self.F == other.F)
        except:
            return False

    def __add__(self, other):
        return self.F.add(self, other)

    def __neg__(self):
        return self.F.neg(self)

    def __sub__(self, other):
        return self.F.sub(self, other)

    def __radd__(self, other):
        return self.__add__(other)

    def __mul__(self, other):
        return self.F.mul(self, other)

    def __rmul__(self, other):
        return self.__mul__(other)

    def __pow__(self, e):
        return self.F.powop(self, e)

    def __div__(self,other):
        return self.F.div(self,other)

    def __truediv__(self,other):
        return self.F.div(self,other)

    def __str__(self):
        return str(self.val)

    def iszero(self):
        return self == self.F.zero()

    def invert(self):
        return self.F.invert(self)

    def invertible(self):
        return self.F.invertible(self)

    def isquadres(self):
        ''' This method return True if the element is a quadratic residue mod q
            different than zero
            it returns False otherwhise
        '''
        if (self+self.F.zero()).iszero() :
            # case of element is zero
            return False
        else :
            # If F's order is prime we use Euler's criterium
            c = self**((self.F.q-1)/2) #TODO: Optimize this
            return c==self.F.one()

    def squareroot(self):
        ''' This method returns the positive square root of
            an element of the field
            using the Tonelli-Shanks algorithm

            Carefull : if the element has no square root, the method does not
            check this case and raises an error. Verification has to be done
            before calling the method.
        '''
        g = self.F.g
        if g == None :
            g = self.F.findnonresidue()
            self.F.g = g

        q = self.F.q

        s=0
        t=self.F.q-1
        while t%2==0:
            s=s+1
            t=t/2
        # q-1 = (2**s)*t

        e = 0
        for i in range(2,s+1):
            b = 2**(i-1)
            b1 = b*2   # b1 = 2**i
            c = ((self)*(g**(-e)))**((q-1)/b1)
            if not c==self.F.one() :
                e = e+b
        h = self*(g**(-e))
        b = (g**(e/2))*(h**((t+1)/2))
        assert b**2 == self # FAILURE to find square root
        return b

    def fingerprint(self):
        return fingexp.fingerprint(self.val)

    def jsonable(self):
        return {'type': 'FieldElem', 'F': self.F, 'val': self.val}


class ExtensionField(Field):
    '''
    This class defines extension fields and inherits field methods.
    Depending on the degree of the extension field, we use
    different algorithms to optimize the operations
    '''
    def __init__(self,F,irpoly,g=None,rep=None):
        '''Define the base Field or extension Field and the irreducible polynomial
           F is the base field on top of which the extension
        field is built
           irpoly is the irreducible polynomial used to build
        the extension field as F/irpoly
           g is a non quadratic residue used to compute square
        roots, if it is set to None, computing a square root
        will initialize g
           rep is the representation of the root of irpoly
        (note that letter 'A' is reserved for the Complex extension field)
        '''
        self.F = F
        self.irpoly = irpoly
        self.deg = len(irpoly.coef) # degree of the irreducible polynomial + 1
        assert self.deg > 0
        self.q = self.F.q**(self.deg-1) # order of the Field

        self.tabular = self.table()

        if rep == None :
            self.rep = rd.choice(['B','C','D','E','F','G','H','J','K','L'])
            #Choose a random representation letter
        else :
            self.rep = rep

        self.char = F.char

        self.primefield = gmpy.is_prime(self.char)

        self.g = g # g is needed to compute square roots, it is a non quadratic residue

        self.to_fingerprint = ["F","irpoly"]
        self.to_export = {"fingerprint": [],"value": ["F","irpoly"]}

    def one(self):
        'unit element for multiplication'
        One = [self.F.zero()]*(self.deg-1)
        One[self.deg-2]= self.F.one()
        return ExtensionFieldElem(self,polynom(self.F,One))

    def zero(self):
        'unit element for addition'
        Zero = [self.F.zero()]*(self.deg-1)
        return ExtensionFieldElem(self,polynom(self.F,Zero))

    def unit(self):
        ''' root of the irreducible polynomial
        e.g. return element 1*A+0 (or the complex value i) if the irpoly is X**2+1
        '''
        I = self.zero()
        I.poly.coef[-2]=self.F.one()
        return I

    def elem(self,x):
        ''' Provided that x belongs to F, return an element of the extension field
            of value x
        '''
        P = self.zero()
        P.poly.coef[-1] = x
        return P

    def random(self):
        ''' Return a random element of the Extension Field
        '''
        polycoef = [0]*(self.deg-1)
        for i in range(self.deg-1):
            polycoef[i] = self.F.random()
        poly = polynom(self.F,polycoef)
        return ExtensionFieldElem(self,poly)

    def __eq__(self, other):
        'testing if we are working in the same extension field'
        try:
            return (self.F == other.F and self.irpoly == other.irpoly)
        except:
            return False

    def add(self, a, b):
        '''
        field operation: addition of polynomial > addition of coefficients in the appropriate field
        '''
        #assert a.F == b.F  and a.F.F == self.F
        if not a.deg == b.deg :
            a = self.reduc(a)
            b = self.reduc(b)
        polysum = [0]*a.deg
        for i in range(a.deg):
            polysum[i]=a.poly.coef[i]+b.poly.coef[i]
        P = polynom(self.F,polysum)
        return ExtensionFieldElem(self,P)

    def sub(self, a, b):
        '''
        field operation: substraction of polynomials > substraction of each coefficient in the appropriate field
        '''
        #assert a.F == b.F and a.F.F == self.F
        if not a.deg == b.deg :
            a = self.reduc(a)
            b = self.reduc(b)
        c = self.neg(b)
        return self.add(a,c)

    def neg(self, a):
        '''
        field operation: opposite of a polynomial > opposite of each coefficient in appropriate field
        '''
        #assert a.F.F == self.F
        ap = [0]*a.deg
        for i in range(a.deg):
            ap[i] = -a.poly.coef[i]
        P = polynom(self.F,ap)
        return ExtensionFieldElem(self,P)

    def smul(self,a,b):
        ''' Return a*b where a or b is scalar
        '''
        if not isinstance(b,FieldElem):
            # b is scalar
            A = a.poly.coef
            Pc = [0]*len(A)
            for i in range(len(Pc)):
                Pc[i] = A[i]*gmpy.mpz(b)
            return ExtensionFieldElem(self,polynom(self.F,Pc))
        else :
            # a is scalar
            return self.smul(b,a)

    def pmul(self,a,b):
        '''Multiplication between polynomials
        '''
        #assert a.F == b.F and a.F.F == self.F
        if not a.deg == b.deg :
            a = self.reduc(a)
            b = self.reduc(b)
        # Simpler notations for reading
        A = a.poly.coef
        B = b.poly.coef

        k = self.deg-1 # degree of the externsion field
        if k == 2 and self.F.rep =='A':
            # We are in the case that the extension field is Fp2
            # We assume here that the irreductible polynom is X**2+1 (beta=-1)
            # Complex multiplication
            a0,a1,b0,b1 = A[0].val,A[1].val,B[0].val,B[1].val
            p = self.char
            v0 = a0*b0
            v1 = a1*b1
            c0 = ((a0+a1)*(b0+b1)-v0-v1)%p
            c1 = (v1-v0)%p
            c0e = FieldElem(c0,self.F)
            c1e = FieldElem(c1,self.F)
            cp = polynom(self.F,[c0e,c1e])
            C = ExtensionFieldElem(self,cp)
            return C
        elif k == 2:
            # In this case, use Karatsuba multiplication algorithm
            # notations
            a0 = A[0]
            a1 = A[1]
            b0 = B[0]
            b1 = B[1]
            beta = -self.irpoly.coef[-1]

            v0 = self.F.pmul(a0,b0)
            v1 = self.F.pmul(a1,b1)
            c0 = self.F.pmul((a0+a1),(b0+b1))-v0-v1 # coefficient of X
            c1 = v1 + self.F.pmul(v0,beta) # independant term
            cp = polynom(self.F,[c0,c1])
            C = ExtensionFieldElem(self,cp)
            return C
        elif k == 3:
            # In this case, use Karatsuba multiplication algorithm
            # notations
            a0,a1,a2 = A
            b0,b1,b2 = B
            beta = -self.irpoly.coef[-1]

            v0,v1,v2 = self.F.pmul(a0,b0), self.F.pmul(a1,b1), self.F.pmul(a2,b2)
            c0 = self.F.pmul((a0+a2),(b0+b2))-v0+v1-v2  # coefficient of X**2
            c1 = self.F.pmul((a2+a1),(b2+b1))-v2-v1+self.F.pmul(beta,v0) # coefficient of X
            c2 = v2+self.F.pmul(beta,(self.F.pmul((a1+a0),(b1+b0))-v1-v0)) # independant term
            cp = polynom(self.F,[c0,c1,c2])
            C = ExtensionFieldElem(self,cp)
            return C

        else :
           prod = convolve(A,B)
           return self.reduc2(prod) # return EProd % ired. polynomial

    def square(self,a):
        ''' This algortihm returns the square of a in the field
            using different methods if the degree of the extension
            is 2,3 or more
        '''
        #print a.F
        #print self
        assert a.F == self

        if not a.deg == self.deg-1 :
            a = self.reduc(a)
        #notations
        A = a.poly.coef
        k = self.deg-1 # degree of the extension

        if k == 2 and self.F.rep == 'A':
            # Using the complex multiplication
            # We are in the case that the extension field is Fp2
            # We assume here that the irreductible polynom is X**2+1 (beta=-1)
            a1, a0 = A[0].val,A[1].val
            p = self.char
            v0 = a0*a1
            c0 = ((a0+a1)*(a0-a1))%p
            c1 = (v0+v0)%p
            c0e = FieldElem(c0,self.F)
            c1e = FieldElem(c1,self.F)
            cp = polynom(self.F,[c1e,c0e])
            C = ExtensionFieldElem(self,cp)
            return C
        elif k == 2:
            # Using the complex multiplication
            a1, a0 = A
            beta = -self.irpoly.coef[-1]
            v0 = self.F.pmul(a0,a1)
            c0 = self.F.pmul((a0+a1),(a0+self.F.pmul(a1,beta)))-v0-self.F.pmul(beta,v0)
            c1 = v0+v0
            cp = polynom(self.F,[c1,c0])
            return ExtensionFieldElem(self,cp)

        elif k == 3:
            # Using Chung-Hasan Squaring2
            a2,a1,a0 = A
            #print a0
            #print 'a0',a0.F, a0.F.deg-1
            #print 'self',self.F, self.F.deg-1
            assert a0.F == self.F
            beta = -self.irpoly.coef[-1]
            s0 = self.F.square(a0)
            t1 = self.F.pmul(a0,a1)
            s1 = t1+t1
            s2 = self.F.square((a0-a1+a2))
            t3 = a1*a2
            s3 = t3+t3
            s4 = self.F.square(a2)

            c0 = s0 + self.F.pmul(beta,s3)
            c1 = s1 + self.F.pmul(beta,s4)
            c2 = s1 + s2 + s3 - s0 -s4
            cp = polynom(self.F,[c2,c1,c0])
            return ExtensionFieldElem(self,cp)

        else :
            return self.F.pmul(a,a)

    def invert(self,a):
        ''' Ths method returns the inverse of a in the field
            The inverse is computed by determining the Bezout coefficient using the
            extended Euclide's algorithm or by specialized algorithms depending
            on the degree of the extension (2 or 3)
        '''
        #assert self.invertible(a) #The element must be invertible
        assert a.F == self
        k = self.deg-1
        if k == 2 and self.F.rep == 'A':
            # inversion in a field of characteristic 2 over prime field
            # We are in the case that the extension field is Fp2
            # We assume here that the irreductible polynom is X**2+1 (mod=-1)
            A = a.poly.coef
            a1,a0 = A[0].val,A[1].val # a = a0+a1*i
            p = self.char

            norm = a0*a0+a1*a1
            invnorm = gmpy.invert(norm,p)
            c0 = (a0*invnorm) % p
            c1 = (-a1*invnorm) % p
            c0e = FieldElem(c0,self.F)
            c1e = FieldElem(c1,self.F)
            invap = polynom(self.F,[c1e,c0e])
            inva = ExtensionFieldElem(self,invap)
            return inva

        elif k == 2 :
            # inversion in a field of characteristic 2 over prime field
            A = a.poly.coef
            a1,a0 = A[0],A[1] # a = a0+a1*i
            #print 'A',A
            #print 'a1',a1
            mod = self.irpoly.coef[-1] # i**2 = -mod
            #a1b,a0b,modb = self.F.elem(a1), self.F.elem(a0),self.F.elem(mod)
            #print 'a1b',a1b
            #a1b2 = self.F.square(a1b)
            a12 = self.F.square(a1)
            #mid = self.F.pmul(a1b2,modb)
            mid = self.F.pmul(a12,mod)
            #norm = self.F.square(a0b)+mid
            norm = self.F.square(a0)+mid
            #invnorm = self.F.invert(a0**2+mod*a1**2)
            #invnorm = self.F.invert(norm.poly.coef[-1])
            invnorm = self.F.invert(norm)
            c = self.F.pmul(a0,invnorm) # c = -a1/(a0**2+mod*a1**2)
            d = -self.F.pmul(a1,invnorm)
            invap = polynom(self.F,[d,c])
            inva = ExtensionFieldElem(self,invap)
            return inva

        elif k == 3 :
            # inversion in char. 3 field
            A = a.poly.coef
            a2,a1,a0 = A[0],A[1],A[2]
            mod = -self.irpoly.coef[-1]
            z0 = self.F.zero()
            z1 = self.F.one()
            if a0 == z0:
                #a0 = 0
                if a1 == z0:
                    #a1 = 0
                    c0,c1,c2 = z0, self.F.invert(self.F.pmul(a2,mod)), z0
                elif a2 == z0:
                    #a2 = 0
                    c0,c1,c2 = z0,z0,self.F.invert(self.F.pmul(a1,mod))
                else :
                    #a1,a2 != 0
                    a22 = self.F.square(a2)
                    a12 = self.F.square(a1)
                    c2 = self.F.pmul(a12,self.F.invert((self.F.pmul(self.F.pmul(a22,a2),mod)+self.F.pmul(self.F.pmul(a12,a1),mod))))
                    c1 = self.F.pmul((z1-self.F.pmul(self.F.pmul(a1,c2),mod)),self.F.invert(self.F.pmul(a2,mod)))
                    c0 = self.F.pmul((-(self.F.pmul(self.F.pmul(a2,mod),c2))),self.F.invert(a1))
            else :
                #a0 != 0
                if a1 == z0 and a2 == z0:
                    #a1 = 0 , a2 = 0
                    c0,c1,c2 = self.F.invert(a0),z0,z0
                else :
                    a12 = self.F.pmul(a1,a2)
                    a12m = self.F.pmul(a12,mod)
                    a00 = self.F.square(a0)
                    abis = a00-a12m

                    if abis == z0:
                        #a0**2-(a1*a2*mod) = 0
                        a11 = self.F.square(a1)
                        a22 = self.F.square(a2)
                        a02 = self.F.pmul(a0,a2)
                        a01 = self.F.pmul(a0,a1)
                        c2 = self.F.pmul(-a,self.F.invert(self.F.pmul((a02-a11),mod)))
                        c1 = self.F.pmul(-a2,self.F.invert(a01-self.F.pmul(a22,mod)))
                        a1c2 = self.F.pmul(a1,c2)
                        a2c1 = self.F.pmul(a2,c1)
                        c0 = self.F.pmul((z1-self.F.pmul(a1c2+a2c1,mod)),self.F.invert(a0))
                    else :
                        #a0**2-(a1*a2*mod) != 0
                        if a1 == z0:
                            #a1 = 0

                            inva0 = self.F.invert(a0)
                            a02 = self.F.pmul(a0,a2)
                            a000 = self.F.pmul(a00,a0)
                            a22 = self.F.square(a2)
                            a222 = self.F.pmul(a22,a2)
                            mm = self.F.square(mod)
                            a222mm = self.F.pmul(a222,mm)

                            c2 = self.F.pmul(-a02,self.F.invert(a000+a222mm))

                            a02m = self.F.pmul(a02,mod)
                            a02mc2 = self.F.pmul(a02m,c2)
                            inva00 = self.F.square(inva0)

                            c1 = self.F.pmul(-a02mc2,inva00)

                            a2m = self.F.pmul(a2,mod)
                            a2mc1 = self.F.pmul(a2m,c1)

                            c0 = self.F.pmul(z1-a2mc1,inva0)
                        elif a2 == z0:
                            #a2 = 0
                            a11 = self.F.square(a1)
                            a111 = self.F.pmul(a11,a1)
                            a000 = self.F.pmul(a00,a0)
                            a111m = self.F.pmul(a111,mod)
                            inva0 = self.F.invert(a0)

                            c2 = self.F.pmul(a11,self.F.invert(a111m+a000))

                            a11m = self.F.pmul(a11,mod)
                            a11mc2 = self.F.pmul(a11m,c2)
                            inva00 = self.F.square(inva0)

                            c1 = self.F.pmul(a11mc2-a1,inva00)

                            a1m = self.F.pmul(a1,mod)
                            a1mc2 = self.F.pmul(a1m,c2)

                            c0 = self.F.pmul(z1-a1mc2,inva0)
                        else :
                            #a1,a2 != 0
                            a01 = self.F.pmul(a0,a1)
                            a22 = self.F.square(a2)
                            a22m = self.F.pmul(a22,mod)
                            a02 = self.F.pmul(a0,a2)
                            a11 = self.F.square(a1)
                            abus = a01-a22m
                            abos = self.F.pmul(a02-a11,mod)
                            invabis = self.F.invert(abis)
                            abb = self.F.pmul(abus,invabis)
                            abb1 = self.F.pmul(abb,a1)
                            abbbos = self.F.pmul(abb,abos)

                            c2 = self.F.pmul(abb1-a2,self.F.invert(abis-abbbos))

                            abosc2 = self.F.pmul(abos,c2)

                            c1 = self.F.pmul(-a1-abosc2,invabis)
                            a1c2 = self.F.pmul(a1,c2)
                            a2c1 = self.F.pmul(a2,c1)

                            c0 = self.F.pmul(z1-self.F.pmul(a1c2+a2c1,mod),self.F.invert(a0))

            invap = polynom(self.F,[c2,c1,c0])
            inva = ExtensionFieldElem(self,invap)
            return inva


        else :
            # inversion in a field of char. != 2,3
            # this inversion takes a longer time (than previous method)
            # it uses extended Euclid's algorithm
            P = ExtensionFieldElem(self,self.irpoly)
            r,u,v = self.extendedeuclide(P,a)
            n,d = r.poly.truedeg()
            assert n == self.deg-2
            c = r.poly.coef[len(r.poly.coef)-1].invert()
            cp = polynom(self.F,[c])
            ce = ExtensionFieldElem(self,cp)
            return ce*v

    def invertible(self,a):
        ''' Return True if a is invertible
        '''
        return not self.reduc(a)==self.zero()

    def div(self,a,b):
        return a*self.invert(b)

    def eucldiv(self,a,b):
        ''' Return a/b and a%b
            a and b are of length d-1 where d is the degree of the irreducible polynomial
        '''
        zero = self.F.zero()
        izero = self.zero()
        d = self.deg
        assert not b.poly.iszero() # Do not divide by zero

        if a.poly.iszero() :
            return izero, izero # quotient is zero, remain is zero
        elif a == b:
            return self.one(), izero # quotient is one, remain is zero

        #Notations
        A = a.poly.coef
        B = b.poly.coef
        n, da = a.poly.truedeg() # position of first non zero elem of a and degree of a
        m, db = b.poly.truedeg() # same for b

        if da<db :
            #  deg(a)<deg(b)
            return izero, a # quotient is zero, remain is a
        elif da==db:
            #deg(a)=deg(b)
            deg = max(d-1,da)
            rc = [zero]*(deg)
            qc = [zero]*(deg)
            q = A[n]/B[m]
            for i in range(1,deg):
                rc[i] = A[n+i]-q*B[m+i]
            qc[deg-1] = q

            rp = polynom(self.F,rc)
            qp = polynom(self.F,qc)
            remain = ExtensionFieldElem(self,rp)
            quotient = ExtensionFieldElem(self,qp)

            return quotient, remain
        else :
            # deg(a)>deg(b)
            deg = max(d-1,da)
            p = deg - da
            rc = [zero]*(deg)
            qc = [zero]*(deg)
            rc[deg-da:] = A[n:]
            pm=0
            while p+pm+db<deg+1:
                #k is the position of the index of the quotient
                k = deg-(da-db)-1+pm
                qc[k] = rc[p+pm]/B[m]
                for i in range(db):
                    rc[i+p+pm] = rc[i+p+pm]- qc[k]*B[m+i]
                pm=pm+1

            rp = polynom(self.F,rc)
            qp = polynom(self.F,qc)
            remain = ExtensionFieldElem(self,rp)
            quotient = ExtensionFieldElem(self,qp)

            return quotient, remain

    def reduc(self,a):
        ''' Return a % self.irpoly
        The polynomial a = [a_0,...,a_n-1] is returned modulo the irreducible polynomial
        The reduced polynomial has length at most d-1 where d is the length
        of the irreducible polynomial
        '''
        assert a.F.F == self.F

        if a.poly.iszero() :
            return self.zero()
        elif a.poly == self.irpoly :
            return self.zero()
        elif a.deg < self.deg :
            c = [self.F.zero()]*(self.deg-1-a.deg)
            newacoef = c+a.poly.coef
            newapoly= polynom(self.F, newacoef)
            newaelem = ExtensionFieldElem(self, newapoly)
            return newaelem
        else :
            # Case where a is not zero or the irreducible polynomial and deg(a)>=deg(irpoly)
            q,r = self.eucldiv(a,ExtensionFieldElem(self,self.irpoly))
            r = self.trunc(r)
            return self.reduc(r)

    def reduc2(self,a):
        ''' a is a list of length (d-1)*2-1 (polynomial length)
            this method returns the equivalent element of length d-1
            using the table of equivalences (build from the irreducible polynomial)
            in the function self.table()
        '''
        As = a[:(self.deg-2)]
        Ad = a[(self.deg-2):]
        b = list(dot(As,self.tabular)+Ad)
        newapoly = polynom(self.F,b)
        newa = ExtensionFieldElem(self,newapoly)
        return newa

    def trunc(self,a):
        '''Return an ExtensionFieldElem of length d-1 where d = deg(irpoly)
        '''
        d = self.deg
        if a.deg == d-1:
            return a
        c = a.poly.coef[a.deg-d+1:] # the (d-1) last elements of a
        cp = polynom(self.F,c)
        return ExtensionFieldElem(self,cp)

    def table(self):
        ''' This method returns a table (usually) stored in self.tabular
           which is used to compute reduction after a multiplication
           between two elements
        '''
        d = self.deg
        T = zeros((d-2,d-1),dtype=object_)
        Pc = self.irpoly.coef[1:]

        for i in range(0,d-2):
           Qc = [self.F.zero()]*(2*(d-1)-1)
           Qc[i+1:i+d] = Pc
           Qp = polynom(self.F,Qc)
           Qe = ExtensionFieldElem(self,Qp)
           Q = self.reduc(-Qe)
           T[i] = array(Q.poly.coef)
        return T

    def extendedeuclide(self,a,b):
        '''Return s,u,v such as s = ua + vb, s is the gcd of a and b
        This method is used to compute the inverse of a mod b (when s=1)
        '''
        #init
        one = self.one()
        zero = self.zero()
        s = a
        u = one
        v = zero
        sp = b
        up = zero
        vp =  one
        #loop : invariants are s = ua+vb and sp = up*a+vp*b
        while not sp.poly.iszero() :
            q,r = self.eucldiv(s,sp)
            s,u,v,sp,up,vp = sp, up, vp, r, u-up*q,v-vp*q

        return self.reduc(s),self.reduc(u),self.reduc(v)

    def __str__(self):
        return str(self.F)+"/"+str(self.irpoly)

    def jsonable(self):
        return {'type': 'Field Extension', 'F': self.F, 'irpoly': self.irpoly, 'degree':self.deg-1}

class ExtensionFieldElem(FieldElem):

    def __init__(self,F,poly):
        '''Define the Extension Field and the representative polynomial
        '''
        self.F = F
        self.poly = poly
        self.siz = len(poly.coef)
        self.deg = self.siz

    def __str__(self):
        x = self.F.rep
        p = self.poly
        s = '('
        if self.siz == 1 :
            s = s+str(p.coef[0])
        if self.siz == 2 :
            s = s+str(p.coef[0])+'*'+x+' + '+str(p.coef[1])
        if self.siz > 2 :
            s =s+str(p.coef[0])+'*'+x+'**'+str(self.siz-1)
            for i in range(1,self.siz-2):
                s = s+' + '+str(p.coef[i])+'*'+x+'**'+str(self.siz-1-i)
            s = s+' + '+str(p.coef[self.siz-2])+'*'+x +' + '+str(p.coef[self.siz-1])
        return s+')'

    def __eq__(self,other):
        try:
            return self.F == other.F and self.poly == other.poly
        except:
            return False

    def fingerprint(self):
        return self.poly.fingerprint()


    def jsonable(self):
        return {'type': 'ExtensionFieldElem', 'F': self.F, 'poly': self.poly, 'size': self.siz}

class polynom:
    ''' This class represents a polynomial written P = c_nX**n+...c_1X+c_0
        c_0,...,c_n are in the Field F (which can be an ExtensionField) so they are either FieldElem or ExtensionFieldElem
        coef is a list : coef = [c_n,...,c_0] of length n+1
    '''
    def __init__(self,F,coef):
        self.F = F # The field in which coeficients belong
        if isinstance(coef,list):
            self.coef = coef # A list of coeficient in decreasing order (by convention) of the polynomial's degree
            self.deg = len(coef) # The degree+1 of the polynomial
        else :
            #coef is not a list but a single element
            self.coef = [coef]
            self.deg = 1

    def __eq__(self,other):
        try:
            return (self.F == other.F and self.coef == other.coef)
        except:
            return False

    def __str__(self):
        # Not consistent with representation letter of the fields
        x = self.F.rep
        if x == None:
            x = 'X'
        s = '('
        if self.deg == 1 :
            s = s+str(self.coef[0])
        if self.deg == 2 :
            s = s+str(self.coef[0])+'*'+x+' + '+str(self.coef[1])
        if self.deg > 2 :
            s =s+str(self.coef[0])+'*'+x+'**'+str(self.deg-1)
            for i in range(1,self.deg-2):
                s = s+' + '+str(self.coef[i])+'*'+x+'**'+str(self.deg-1-i)
            s = s+' + '+str(self.coef[self.deg-2])+'*'+x +' + '+str(self.coef[self.deg-1])
        return s+')'

    def fingerprint(self):
        L = []
        for c in self.coef:
            L.append(c.fingerprint())
        return fingexp.fingerprint(L)

    def iszero(self):
        '''Return True if it is a zero polynomial (each coefficient is zero)
           This does not return True if the polynomial is the polynomial that generates the extension field
        '''
        cond = True
        for i in self.coef:
            pcond = i.iszero()
            cond = pcond*cond
        return cond

    def truedeg(self):
        '''Return the position of the first non zero coefficient and the actual degree of the polynomial
        '''
        if self.iszero():
            return 0,0
        n = 0
        while self.coef[n]==self.F.zero():
            n = n+1
        # n  is the position of the first non zero coeff of the polynomial
        return n, self.deg-n  # position and actual degree of the polynomial

    def jsonable(self):
        return {'type': 'polynomial', 'F': self.F, 'coeficients': self.coef, 'degree': self.deg}


