# -*- coding: utf-8 -*-

import field
#import gmpy
import tools.fingexp as fingexp

class ECGroup(fingexp.FingExp):
    'Class for Elliptic Curve Group'

    def __init__(self,F,E,infty):
        ''' F is the Field for arithmetic operations (type :Field)
            E is an elliptic curve Y**2=X**2+aX+b (type :Curve)
            infty is a point at infinity (type :ECPoint)
        '''
        assert isinstance(F,field.Field)
        assert isinstance(E,Curve)
        assert isinstance(infty,ECPoint) and infty.infty == True
        self.F = F
        self.F0 = self.F.zero()
        self.F1 = self.F.one()
        self.E = E
        self.infty = infty
        self.infty.set_ECG(self) # Make the point at infinity belong to the EC group

        self.to_fingerprint = ["F","E"]
        self.to_export = {"fingerprint": [],"value": ["F","E"]}

    def __eq__(self,other):
        try:
            return (self.F == other.F and self.E == other.E and self.infty == other.infty)
        except:
            return False

    def elem(self,x=None,y=None,z=1,Jcoord=False):
        '''return a new element of the curve with coordinate x,y
           !!! This method does not check if the point is actually on the curve!!!
           if x or y is None, return if possible a y-matching
           or x-matching element on the curve
           if both x,y are None, return a random element of the curve
        '''
        if not x == None and not y == None:
            if isinstance(x,field.FieldElem) and isinstance(x,field.FieldElem) :
                return ECPoint(x,y,z,ECG=self,infty=False,Jcoord=Jcoord)
            else:
                return ECPoint(field.FieldElem(x,self.F),field.FieldElem(y,self.F),field.FieldElem(z,self.F),ECG=self,infty=False,Jcoord=Jcoord)

        elif not x == None and  y == None:
            xval = x**3+self.E.a*x+self.E.b
            if not xval.isquadres():
                return None
            else:
                y = xval.squareroot()
                return ECPoint(x,y,z,ECG=self,infty=False,Jcoord=Jcoord)
        elif x == None and not y == None:
            #TODO :"Generate a random element on the curve matching y = ",y,"\n method not implemented yet"
            return None
        elif x == None and  y == None:
             #Generate a random element on the curve
            return self.random()

    def random(self):
        ''' This method returns a random element of the curve
            it recursively try to find a random element on the
	    curve
        '''
        x = self.F.random()
        P = self.elem(x=x)
        if P == None :
            return self.random()
        else :
            return P

    def arandom(self,n=1):
        ''' This method returns a list of n random elements of the curve
        '''
        assert n>=1
        L = []
        for i in range(n):
            P = self.random()
            L.append(P)
        return L


    def neg(self,P):
        '''Return opposite element of P = (x,y) : -P = (x,-y)
        '''
        if P.infty :
            return P
        elif not P.Jcoord :
            return ECPoint(P.x,-P.y,z=self.F1,ECG=self)
        else :
            return ECPoint(P.x,-P.y,P.z,ECG=self,Jcoord = True)

    def double(self,P):
		'''doubling assuming P is an ECpoint of the current ECgroup
		This method returns [2]P
		'''
                if P.y == self.F0:
                    # P is on x-axis : P+P = O
                    return self.infty
                else:
                    if not P.Jcoord :
                        # In affine coordinates
                        l= (self.F.smul(P.x**2,3)+self.E.a)/(self.F.smul(P.y,2))
                        x3= l**2-self.F.smul(P.x,2)
                        y3= (P.x-x3)*l-P.y
                        return ECPoint(x3,y3,ECG=self)
                    else :
                        # In Jacobian coordinates
                        M = 3*P.x**2+self.E.a*(P.z**4)
                        R = P.y**2
                        S =  4*P.x*R
                        x3 = M**2-2*S
                        y3 = M*(S-x3)-8*R**2
                        z3 = 2*P.y*P.z
                        return ECPoint(x3,y3,z3,ECG=self,infty = z3==self.F0,Jcoord = True)

    def dadd(self,P,Q,tab=None):
        '''addition assuming P != Q are two ECpoints of the current ECgroup
        This method returns P+Q
        tab must be of the form A,B,C,D
        '''

        if tab == None :
            b,A,B,C,D = self.equal(P,Q)
        else :
            A,B,C,D = tab

        if P.x == Q.x :
            # P and Q have same x coordinate (but not same y) : P+Q = O
			return self.infty
        else:
            if not P.Jcoord :
                # In affine coordinates
                l = (Q.y-P.y)/(Q.x-P.x)
                x3 = l**2-P.x-Q.x
                y3 = (P.x-x3)*l-P.y
                return ECPoint(x3,y3,ECG=self)
            else :
                # In Jacobian coordinates
                if A==B :
					# case where Px = Qx (in Jacobian coordinates)
                    return self.infty
                #Qz2 = Q.z**2
                #Pz2 = P.z**2
                #U1 = P.x*Qz2
                #U2 = Q.x*Pz2
                #S1 = P.y*Qz2*Q.z
                #S2 = Q.y*P.z*Pz2
                E = B-A
                F = D-C
                E2 = E**2
                E3 = E2*E
                AE2 = A*E2
                x3 = F**2-E3-2*AE2
                y3 = F*(AE2-x3)-C*E3
                z3 = P.z*Q.z*E
                return ECPoint(x3,y3,z3,ECG=self,infty = z3==self.F0,Jcoord = True)

    def equal(self,P,Q):
        '''
        Return a boolean stating if P==Q and 4 values needed for the
        computation of P+Q
        '''
        if not P.Jcoord and not Q.Jcoord :
			#Affine coord.
            return (P==Q),0,0,0,0
        elif P.Jcoord and not Q.Jcoord :
            Pz2 = P.z**2
            Pz3 = Pz2*P.z
            A = P.x
            B = Q.x*Pz2
            C = P.y
            D = Q.y*Pz3
            return (A==B and C==D),A,B,C,D
        elif not P.Jcoord and Q.Jcoord :
            Qz2= Q.z**2
            Qz3 = Qz2*Q.z
            A = P.x*Qz2
            B = Q.x
            C = P.y*Qz3
            D = Q.y
            return (A==B and C==D),A,B,C,D
        else:
            #both points in Jacobian coord.
            Pz2 = P.z**2
            Pz3 = Pz2*P.z
            Qz2= Q.z**2
            Qz3 = Qz2*Q.z
            A = P.x*Qz2
            B = Q.x*Pz2
            C = P.y*Qz3
            D = Q.y*Pz3
            return (A==B and C==D),A,B,C,D

    def add(self,P,Q):
        '''
        group operation : addition of points P and Q over EC
        '''
        #if not isinstance(P,ECPoint) or not isinstance(Q,ECPoint):
        #    raise Exception("Cannot add non ECPoint")

        if P.infty == True :
            return Q
        elif Q.infty  == True :
            return P
        elif not P.ECG == Q.ECG :
            raise Exception("Cannot add ECPoint of different EC")
        else :
            b,A,B,C,D = self.equal(P,Q)
            if b:
				return self.double(P)
            else:
				return self.dadd(P,Q,[A,B,C,D])

    def sub(self,P,Q):
        ''' Return P-Q
        '''
        return self.add(P,self.neg(Q))

    def mul(self,P,alpha):
        ''' multiplication of P by a scalar or FieldElem alpha
        '''
        if alpha == 0 :
            # multiplication by zero returns point at infinity
            return self.infty
        elif alpha<0:
            return -self.mul(P,-alpha)
        #elif alpha > self.F.char :
            #TODO : check this
            #return self.mul(P,alpha%self.F.char)
        else :
            return self.dbleAndAdd(P,alpha)

    def dbleAndAdd(self,P,n):
        'return n*P using double and add technique'

        if n == 0 :
            return self.infty
        elif n == 1 :
            return P
        elif n%2 == 1 :
            Q = self.dbleAndAdd(P,(n-1)/2)
            return P+Q+Q
        elif n%2 == 0 :
            Q = self.dbleAndAdd(P,n/2)
            return Q+Q

    def __str__(self):
        return "Elliptic Curve Group E("+str(self.E)+")"


    def jsonable(self):
        print "Elliptic Curve Group over the field F = ", self.F, " on the curve E = ",self.E," with infinity point O = ",self.infty

class Curve(fingexp.FingExp):
    'Class defining Elliptic Curve Polynomial on Weirstrass form for Elliptic Curve Group'
    def __init__(self,a,b,F):
        '''
        Y**2 = X**3 + aX + b over F
        '''
        assert isinstance(a,field.FieldElem)
        assert isinstance(b,field.FieldElem)
        assert a.F == F
        assert b.F == F
        self.a = a
        self.b = b
        self.F = F

        self.to_fingerprint = ["F","a","b"]
        self.to_export = {"fingerprint": [],"value": ["F","a","b"]}

    def __str__(self):
        return "Y**2 =  X**3 + "+str(self.a)+"*X + "+str(self.b)+" over "+str(self.F)

    def jsonable(self):
        return {'type': 'Elliptic Curve', 'F': self.F, 'a': self.a , 'b':self.b}

class ECPoint:
    'Class for points over Elliptic Curve'

    def __init__(self,x=None,y=None,z=None,ECG=None,infty=False,Jcoord = False):
        ''' x the x-coordinate
            y the y-coordinate
            z the z-coordinate is used if Jcoord is True
            ECG the Elliptic Curve Group of the ECPoint
            infty is True if the ECPoint is the neutral element
            Jcoord is False if the affine coordinates are used and True if the
            Jacobian coordinates are used
        '''
        self.ECG = ECG
        self.infty = infty #set to True for the neutral element
        self.x = x
        self.y = y
        self.z = z #z is the third jacobian coordinate
        self.Jcoord = Jcoord # if True, the Jacobian coordinate is used

    def isOnCurve(self):
        ''' Return True if the point belongs to the curve
        '''
        E = self.ECG.E
        if self.infty :
            return True
        elif not self.Jcoord :
            return (self.y**2 == self.x**3+E.a*self.x+E.b)
        else:
            assert not self.z == self.ECG.F.zero() # Point is at infinity but attribute infty is not set to true
            Y = self.y/self.z**3
            X = self.x/self.z**2
            return (Y**2 == X**3+E.a*X+E.b)

    def toJcoord(self):
        ''' Convert a point in affine coordinate into a point in Jacobian coordinate
        '''
        if self.Jcoord:
            return self
        else :
            self.Jcoord = True
            F = self.ECG.F
            if self.infty :
                self.z = F.zero()
            else :
                self.z = F.one()
    def toAffine(self):
        '''Convert a point in Jacobian coordinate into a point in Affine coordinate
        '''
        if not self.Jcoord:
            return self
        else :
            self.Jcoord = False
            F = self.ECG.F
            if self.z == F.zero() :
                self.infty = True
            else :
                self.x = self.x/(self.z**2)
                self.y = self.y/(self.z**3)

    def copy(self):
        return ECPoint(self.x,self.y,self.z,self.ECG,self.infty,self.Jcoord)

    def __eq__(self,other):
        ''' Test equality between two EC points
        '''
        if not isinstance(other, ECPoint):
            return False
        elif self.infty == True or other.infty == True :
            try :
                return (self.infty == other.infty and self.ECG.F == other.ECG.F and self.ECG.E == other.ECG.E)
            except :
                return False
        elif self.Jcoord == True and other.Jcoord == True :
            if (self.x == other.x and self.y == other.y and self.z == other.z):
                try:
                    return (self.ECG.F == other.ECG.F  and self.ECG.E == other.ECG.E)
                except:
                    return False
            else :
                A = (self.x)*((other.z)**2)
                B = (other.x)*((self.z)**2)
                C = (self.y)*((other.z)**3)
                D = (other.y)*((self.z)**3)
                try:
                    return (self.ECG.F == other.ECG.F  and self.ECG.E == other.ECG.E and A==B and C==D)
                except:
                    return False

        elif self.Jcoord == False and other.Jcoord == False :
             try:
                 return (self.ECG.F == other.ECG.F  and self.ECG.E == other.ECG.E and self.x == other.x and self.y == other.y)
             except:
                return False

        elif self.Jcoord == True and other.Jcoord == False :
            assert not self.z == self.ECG.F.zero() # Error : self.infty is False but self.z == 0
            X = self.x/(self.z**2)
            Y = self.y/(self.z**3)
            try :
                return (self.ECG.F == other.ECG.F and self.ECG.E == other.ECG.E and X == other.x and Y == other.y)
            except :
                return False
        elif self.Jcoord == False and other.Jcoord == True :
            assert not other.z == other.ECG.F.zero() # Error : other.infty is False but other.z == 0
            X = other.x/(other.z**2)
            Y = other.y/(other.z**3)
            try :
                return (self.ECG.F == other.ECG.F and self.ECG.E == other.ECG.E and X == self.x and Y == self.y)
            except :
                return False

    def __str__(self):
        if not self.Jcoord :
            if self.infty:
                return "EC point at infinity"
            else:
                return "EC point ("+str(self.x)+" ,"+str(self.y)+")"
        else :
            if self.infty:
                return "EC point at infinity in Jcoord"
            else:
                return "EC point in Jcoord ("+str(self.x)+" ,"+str(self.y)+" ,"+str(self.z)+")"

    def __repr__(self):
        return self.__str__()

    def __neg__(self):
        if self.infty == True :
            return self
        else :
            return self.ECG.neg(self)

    def __add__(self,other):
        return self.ECG.add(self,other)

    def __sub__(self,other):
        return self.ECG.sub(self,other)

    def __mul__(self,other):
        return self.ECG.mul(self,other)

    def __rmul__(self,other):
        return self.ECG.mul(self,other)


    def set_ECG(self,ECG):
        """ Set the ECG of the 'point at infinity'
        """
        assert self.ECG ==  None
        assert self.infty == True
        self.ECG = ECG

    def fingerprint(self):
        if self.Jcoord :
            return fingexp.fingerprint((self.ECG,self.infty,self.x,self.y,self.z,self.Jcoord))
        else :
            return fingexp.fingerprint((self.ECG,self.infty,self.x,self.y,self.Jcoord))

    def jsonable(self):
        if self.infty :
            print "Point at infinity over the Elliptic Curve Group = ",self.ECG
        elif self.Jcoord :
            print "Point over the Elliptic Curve Group = ",self.ECG," of Jacobian coordinates \n x = ",self.x,"\n y = ",self.y,"\n z =",self.z
        else :
            print "Point over the Elliptic Curve Group = ",self.ECG," of coordinates \n x = ",self.x,"\n y = ",self.y
