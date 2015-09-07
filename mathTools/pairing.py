# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

import field
import gmpy
import tools.fingexp as fingexp
import tools.utils as utils


class Pairing(fingexp.FingExp):
    ''' This class initialize the pairing on groups G1 x G2
        Where G1 =  <P> is a subgroup of order r of an Elliptic Curve Group E[F_q]
        and G2 =  <Q> is a subgroup of order r of an Elliptic Curve Group E[F_(q^p)]
        E is an elliptic curve (over Fqp)
        with r,q coprime

        - frob is the frobenius endomorphism. It helps to compute a**(p**i) an
        element a of Fpk given as inputs (a,gamma,i)
        where gamma is a precomputed table used to compute f and fast multiplications
        in EFpk
        beta is a precomputed table used to compute hard exponent
        (see otosEC.py for these tables)
    '''
    def __init__(self, EFp, EFpk, E, P, Q, r, Qp=None, frob=None, gam=None, bet = None):
        self.E = E #Elliptic Curve (equation) over EFp
        self.EFp = EFp # Elliptic Curve Group
        self.Fp = EFp.F # Field of the ECG
        self.Fp1 = self.Fp.one()
        self.Fp0 = self.Fp.zero()
        self.EFpk = EFpk
        self.Fpk = EFpk.F
        self.Fpk1 = self.Fpk.one()
        self.Fpk0 = self.Fpk.zero()

        self.frobenius = frob
        self.gamma = gam
        #self.beta = bet

        self.P = P # Generator of G1
        self.Q = Q # Generator of G2
        #self.Qp = Qp
        self.r = r # This is the order of the subgroups G1, G2
        def degext(M,L):
            '''Return the degree of the extension of M over L (provided M,L are Fields)
            Assuming M is an extension of L
            '''
            assert isinstance(M,field.Field) and isinstance(L,field.Field)
            k = 1
            while not M.F == M:
                k = k*(M.deg-1)
                M = M.F
                if M == L :
                    return k
        k = degext(self.Fpk,self.Fp) # This is the degree of the extension EFpk over EFp
        q = self.Fp.char-1

        self.e = gmpy.divexact(q**(k)-1,self.r)


        self.to_fingerprint = ["E","EFp","EFpk","r"]
        self.to_export = {"fingerprint": [],"value": ["E","EFp","EFpk","r"]}


    def load(self, data, fingerprints):
        self.E = utils.b64tompz(data["E"])
        self.EFq = utils.b64tompz(data["EFp"])
        self.EFqp = utils.b64tompz(data["EFpk"])
        self.r = utils.b64tompz(data["r"])

    def __str__(self):
        return "Pairing with\n G1 = < "+str(self.P)+" > in "+str(self.EFp)+"\n G2 = < "+str(self.Q)+" > in "+str(self.EFpk)+"\n of order r="+str(self.r)

    def hardexpo(self,m):
        ''' return m**((p**4-p**2+1)/r)
        where u = gamma[6] is the parameter of p(u)
        gamma is a table of precomputed values to
        compute the frobenius
        Algorithm comes from [Scott et Al, Pairing 2009]
        http://eprint.iacr.org/2008/490.pdf
        '''
        frob = self.frobenius
        g = self.gamma
        u = self.g[6]
        m1 = m**u
        m2 = m1**u # m**(u**2)
        m3 = m2**u # m**(u**3)

        invm = self.Fpk.invert(m) # 1/m
        invm1 = self.Fpk.invert(m1) # 1/(m**u)
        invm2 = self.Fpk.invert(m2) # 1/(m**(u**2))
        invm3 = self.Fpk.invert(m3) # 1/(m**(u**3))

        y0 = frob(m,g)*frob(m,g,2)*frob(m,g,3) # (m**p)*(m**(p**2))*(m**(p**3))
        y1 = invm
        y2 = frob(m2,g,2) # (m**(u**2))**(p**2)
        y3 = frob(invm1,g) # (1/m**u)**p
        y4 = invm1*frob(invm2,g) # (1/m**u)*(1/m**(u**2))**p
        y5 = invm2
        y6 = invm3*frob(invm3,g) # (1/m**(u**3))**(p+1)

        T0 = y6**2
        T0 = T0*y4
        T0 = T0*y5
        T1 = y3*y5
        T1 = T1*T0
        T0 = T0*y2
        T1 = T1**2
        T1 = T1*T0
        T1 = T1**2
        T0 = T1*y1
        T1 = T1*y0
        T0 = T0**2
        T0 = T0*T1

        return T0

###################################################################################
######################### Tate Pairing ############################################
###################################################################################

    def TatePairing(self,P,Q,Pair=None,Jcoord = False):
        ''' This method evaluates the Tate pairing using Miller's algorithm
            e(P,Q) where P belongs to G1 and Q to G2
            Remark that the output x has to be raised to the power of
            (q**k-1)/r to belong to the r-torsion group
            where q =  |Fq| and k is the degree of the extension Fqp over Fq
        - P is in EFp
        - assuming Q is in EFpk
        '''
        # Notations
        frob = self.frobenius
        g = self.gamma
        ##################### Functions used in the Tate pairing ##################
        def line(U,V):
            ''' This method returns a,b,c in F such as aY+bX+c is the equation
            of the line through U and V two points of an elliptic curve
            if U or V is the point at infinity, the method returns 0,0,1 (in F)
            if U = V, the method returns the tangent of E in U
            if U = -V, the method returns the vertical line (of course)
            '''
            if U.infty == True or V.infty == True :
                a,b,c = self.Fp0, self.Fp0, self.Fp1
                return [a,b,c]
            if U.x == V.x and not  U.y == V.y :
                a,b,c = self.Fp0, self.Fp1, -U.x
                return [a,b,c]
            # 0*Y+1*X-U.x

            Ux = U.x
            Uy = U.y

            if U == V :
                Ea = self.E.a
                a = 2*Uy
                Ux2 = 3*Ux*Ux
                b = -(Ux2+Ea)
                c = -(a*Uy)+(Ux2+Ea)*Ux

            else :
                # case U neq V
                Vx = V.x
                Vy = V.y

                a = Vx-Ux
                b = Uy-Vy
                c = Vy*Ux-Uy*Vx#(Vy-Uy)*Ux-(Uy*(Vx-Ux))

            return [a,b,c]

        def evaluate(P,coef):
            ''' Evaluate P on the line aY+bX+c where coef[0] = a, coef[1] = b,
            coef[2] = c
            '''

            a = coef[0].val
            b = coef[1].val
            c = coef[2].val

            e = a*P.y+b*P.x+c*self.Fpk1
            return e

        ############## Algorithm for the Tate Pairing #############################

        #init
        x = self.Fpk1
        Z = P
        rbin = bin(self.r)
        t = len(rbin)-1 # r = r_2...r_t where r_i is in {0,1} the bit repr. of r

        #loop
        for i in range(3,t+1):
            TZQ = evaluate(Q,line(Z,Z))
            ZZ = Z+Z
            x = x*x*TZQ
            Z = ZZ
            if rbin[i]=='1':
                LZPQ = evaluate(Q,line(Z,P))
                ZP = Z+P
                x = x*LZPQ
                Z = ZP

        if frob == None :
            y = x**self.e # standardizing x to belong to the correct group
        else :
            # here we use the frobenius endomorphism to compute q-th powers
            # we use formulae proposed in [Devegili et al 07]

            xinv = self.Fpk.invert(x)
            x1 = frob(x,g,6)*xinv # x**(p**6-1)
            x2 = frob(x1,g,2)*x1  # x1**(p**2+1)

            # what follows will provide x2**((p**4-p**2+1)/r)
            # so that at last, we have y = x**((p**12-1)/r)
            y = self.hardexpo(x2,g)

        return y

###################################################################################
######################### Ate Pairing #############################################
###################################################################################

    def AtePairing(self,P,Q,Pair=None,Jcoord = False):
        '''
        P is an EC point over E[Fp]
        Q is an EC point over E'[Fp2]
        t is the trace of frobenius of the curve E
        The algorithm outputs the Ate Pairing of (P,Qp) where Qp = psi(Q)
        '''

        ##################### Functions used in the Ate pairing ###################
        def line(U,V):
            ''' This method returns a,b,c in F such as aY+bX+c is the equation
            of the line through U and V two points of an elliptic curve

            if U or V is the point at infinity, the method returns 0,0,1 (in F)
            if U = V, the method returns the tangent of E in U
            if U = -V, the method returns the vertical line (of course)

            '''

            if U.infty == True or V.infty == True :
                a,b,c = self.Fpk0, self.Fpk0, self.Fpk1
                return [a,b,c]

            if U.x == V.x and not  U.y == V.y :
                a,b,c = self.Fpk0, self.Fpk1, -U.x
                return [a,b,c]
                # 0*Y+1*X-U.x

            Ux = U.x
            Uy = U.y

            if U == V :
                Ea = self.EFpk.E.a
                a = 2*Uy
                Ux2 = 3*Ux*Ux
                b = -(Ux2+Ea)
                c = -(a*Uy)+(Ux2+Ea)*Ux
            else :
                # case U neq V
                Vx = V.x
                Vy = V.y

                a = Vx-Ux
                b = Uy-Vy
                c = Vy*Ux-Uy*Vx

                return [a,b,c]

        def evaluate(P,coef):
            ''' Evaluate P on the line aY+bX+c where coef[0] = a, coef[1] = b, coef[2] = c
            '''

            a = coef[0]
            b = coef[1]
            c = coef[2]

            e = a*P.y.val+b*P.x.val+c

            return e
        ############## Algorithm for the Ate Pairing #############################
        # Notations
        frob = self.frobenius
        g = self.gamma
        u = g[6]
        psi = g[7]
        # init
        T = Q
        x = self.Fpk1
        tbin = bin(6*u+2)
        l = len(tbin)
        # loop
        for i in range(4,l):
            Tp = psi(T)
            LTT = evaluate(P,line(Tp,Tp))
            x = (x**2)*LTT
            T = T+T
            if tbin[i] == '1':
                Tp = psi(T)
                LTQ = evaluate(P,line(Tp,psi(Q)))
                x = x*LTQ
                T = T+Q
        # final expo
        if u<0:
           T = -T
           x = self.Fpk.invert(x)
        Tp = psi(T)
        Qp = psi(Q)
        Q1x = frob(Qp.x,g,1)
        Q1y = frob(Qp.y,g,1)
        Q2x = frob(Q1x,g,1)
        Q2y = frob(Q1y,g,1)
        Q1 = self.EFpk.elem(Q1x,Q1y)
        Q2 = self.EFpk.elem(Q2x,Q2y)

        LTQ1 = evaluate(P,line(Tp,Q1))
        x = x*LTQ1
        Tp = Tp+Q1
        LTQ2 = evaluate(P,line(Tp,-Q2))
        x = x*LTQ2

        # here we use the frobenius endomorphism to compute q-th powers
        # we use formulae proposed in [Devegili et al 07]
        xinv = self.Fpk.invert(x)
        x1 = frob(x,g,6)*xinv # x**(q**6-1)
        x2 = frob(x1,g,2)*x1  # x1**(q**2+1)

        y = self.hardexpo(x2,g)
        #y = x**((p**k-1)/r)
        return y

    def precomp(self,Q):
        ''' This method could be useful if one needs to compute many
            ate pairing Ate(P,Q) over the same Q (for different P)
        '''
        u = self.gamma[6]
        tbin = bin(abs(6*u+2))
        l = len(tbin)
        L = []
        T = Q
        for i in range(3,l):
            L.append(T)
            T = T+T
            if tbin[i]=='1':
                L.append(T)
                T = T+Q
        L.append(T)
        return L
