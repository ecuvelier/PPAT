"""
import os, sys, inspect
# realpath() will make your script run, even if you symlink it :)
cmd_folder = os.path.realpath(os.path.abspath(os.path.split(inspect.getfile( inspect.currentframe() ))[0]))
if cmd_folder not in sys.path:
    sys.path.insert(0, cmd_folder)

# use this if you want to include modules from a subfolder
cmd_subfolder = os.path.realpath(os.path.abspath(os.path.join(os.path.split(inspect.getfile( inspect.currentframe() ))[0],"math")))
if cmd_subfolder not in sys.path:
     sys.path.insert(0, cmd_subfolder)

cmd_subfolder = os.path.realpath(os.path.abspath(os.path.join(os.path.split(inspect.getfile( inspect.currentframe() ))[0],"ppat")))
if cmd_subfolder not in sys.path:
     sys.path.insert(0, cmd_subfolder)

cmd_subfolder = os.path.realpath(os.path.abspath(os.path.join(os.path.split(inspect.getfile( inspect.currentframe() ))[0],"nizkproofs")))
if cmd_subfolder not in sys.path:
     sys.path.insert(0, cmd_subfolder)
"""

import mathTools.field as field
import mathTools.ellipticCurve as ellipticCurve
import mathTools.pairing as pairing
#import ppat.ppats as ppats
import ppat.ppats
import mathTools.otosEC as oEC

import gmpy
from Crypto.Random.random import randint


###################################################################################
################## Building a pairing on BN Curves ################################ ###################################################################################
###################################################################################
# PARAMETERS come from paper :
# A family of Implementation-Friendly BN Elliptic Curves
# Pereira et al 2009 Journal of System and Softwares
# http://www.sciencedirect.com/science/article/pii/S0164121211000914

#sys.setrecursionlimit(10000)

#c = gmpy.mpz(2) # p is 160-bit long
c = gmpy.mpz(1) # p is 256-bit long
d = gmpy.mpz(1)
b = c**4+d**6 # b = c**4+d**6
#u = gmpy.mpz(-(2**38 + 2**28 + 1 )) # p is 160-bit long
u = gmpy.mpz(-(2**62 + 2**55 + 1 )) # p is 256-bit long
#p = 36*u**4 + 36*u**3 + 24*u**2 + 6*u + 1
def pr(u):
    return 36*u**4 + 36*u**3 + 24*u**2 + 6*u + 1
def nr(u):
    return 36*u**4 + 36*u**3 + 18*u**2 + 6*u + 1
p = pr(u)
n = nr(u)
#n = 36*u**4 + 36*u**3 + 18*u**2 + 6*u + 1
#n is 160-bit long with low HW
t = 6*u**2 + 1

##### Fp #####
Fp = field.Field(p)
fp0 = Fp.zero()
fp1 = Fp.one()

print Fp, " ...done"
##### E[Fp] #####
C = ellipticCurve.Curve(fp0,b*fp1,Fp) # Y**2 = X**3+b
PInf = ellipticCurve.ECPoint(infty = True)
EFp = ellipticCurve.ECGroup(Fp,C,PInf)
P = EFp.elem((-d**2)*fp1,(c**2)*fp1)  # P  is a generetor of EFp of order n (n*P = Pinf)


##### Fp2b #####
poly1 = field.polynom(Fp,[fp1,fp0,fp1]) # X**2+1
print poly1

Fp2 = field.ExtensionField(Fp,poly1,rep='i') # A**2 = -1
print Fp2, " ...done"
fp2_0 = Fp2.zero()
fp2_1 = Fp2.one()
fp2_ip = field.polynom(Fp,[fp1,fp0]) # 1*A+0
fp2_i = field.ExtensionFieldElem(Fp2,fp2_ip)
xi = (c**2)*fp2_1+(d**3)*fp2_i # c**2+(d**3)*A (4+i)
cxi = (c**2)*fp2_1-(d**3)*fp2_i # c**2-(d**3)*A
#ixi = 8*fp2bi-8*fp2b1 # 8*A-8
#xi = ixi.invert()
#C2b = EllipticCurve.Curve(fp2b0, 3*ixi,Fp2b) # Y**2 = X**3+3*(8*A-8)
C2 = ellipticCurve.Curve(fp2_0, cxi,Fp2) # Y**2 = X**3+c**2-(d**3)*A The twisted curve
PInf2 = ellipticCurve.ECPoint(infty = True)
EFp2 = ellipticCurve.ECGroup(Fp2,C2,PInf2)

u0 = EFp2.elem((-d)*fp2_i,c*fp2_1) #EC point (-d*A,c)
h = 2*p-n
Q = u0*h # Q is a generator of G2 of order n

r= randint(1,int(n))
s= randint(1,int(n))
rP = r*P
sQ = s*Q


##### Fp6 #####
poly3 = field.polynom(Fp2,[fp2_1,fp2_0,fp2_0,-xi]) #X**3-xi
Fp6 = field.ExtensionField(Fp2,poly3)
fp6_0 = Fp6.zero()
fp6_1 = Fp6.one()
fp6_xi = Fp6.elem(xi) # xi in Fp6

##### Fp12 #####
poly6 = field.polynom(Fp6,[fp6_1,fp6_0,-fp6_xi]) # X**2-xi
Fp12 = field.ExtensionField(Fp6,poly6)
print Fp12, " ...done"
fp12_0 = Fp12.zero()
fp12_1 = Fp12.one()
C12 = ellipticCurve.Curve(fp12_0,b*fp12_1,Fp12) # Y**2 = X**3+b
PInf12 = ellipticCurve.ECPoint(infty = True)
EFp12 = ellipticCurve.ECGroup(Fp12,C12,PInf12)

Qpr = oEC.psi(EFp12,Q) # Qpr lives in E[Fp12b]
Pair = pairing.Pairing(EFp,EFp12,C,P,Q,n,Qpr,oEC.frobenius,oEC.prec_gamma(Fp12,u,c,d))

x1 = randint(1,int(n-1));print "x1 is", x1
g1 = x1*Q
h1td = randint(1,int(n-1));print "h1 trapdoor is", h1td
h1 = h1td*P
ppatspp = ppat.ppats.PPATSPublicParameters(P,Q,Pair,'Ate', optim = True)
print 'public parameters ppatspp created'
ppatspk = ppat.ppats.PPATSPublicKey(ppatspp,g1,h1)
print 'public key ppatspk created'
ppatssk = ppat.ppats.PPATSPrivateKey(ppatspp,ppatspk,x1)
print 'secret key ppatssk created'
