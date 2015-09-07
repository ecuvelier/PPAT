# -*- coding: utf-8 -*-
"""
Created on 2013-2014

Author : Edouard Cuvelier
Affiliation : Université catholique de Louvain - ICTEAM - UCL Crypto Group
Address : Place du Levant 3, 1348 Louvain-la-Neuve, BELGIUM
email : firstname.lastname@uclouvain.be
"""

import random
import numpy
#import time
from script import Fp

def ope1(A,l1,l2):
    B = A.copy()
    L1 = A[l1].copy()
    L2 = A[l2].copy()
    B[l1] = L2
    B[l2] = L1
    return B

def ope2(A, alpha, l):
    B = A.copy()
    L = A[l].copy()
    L = rowmul(L,alpha)
    B[l] = L
    return B

def ope3(A,alpha,l1,l2):
    # l1 = l1+alpha*l2
    B = A.copy()
    L1 = A[l1].copy()
    L2 = A[l2].copy()
    L1 = L1+rowmul(L2,alpha)
    B[l1] = L1
    return B

def rowmul(Lp,alpha):
    L = Lp.copy()
    for i in range(len(L)) :
        L[i] = alpha*L[i]
    return L

def pivot(A,l,zero):
    L = A[l]
    k = len(L)
    pivot = None
    i = -1
    while (pivot == None or pivot == zero) and i < k-1 :
        i = i+1
        pivot = L[i]
    if pivot == zero or pivot == None :
        return i+1,None
    else :
        return i,pivot

def pivotlist(A,zero):
    m = len(A) #nb of rows
    pivotl = []
    for i in range(m):
        pos,piv = pivot(A,i,zero)
        pivotl.append((pos,piv,i))
    return pivotl

def sortrows(A,zero):
    m = len(A) #nb of rows
    n = len(A[0]) #nb col
    pivotl = pivotlist(A,zero)
    pivotl.sort()
    B = numpy.zeros((m,n))
    for j in range(m):
        i = pivotl[j][2]
        B[j] = A[i]
    return B

def sortmat(A,B,zero):
    m = len(A) #nb of rows
    pivotl = pivotlist(A,zero)
    L = pivotl+[]
    for i in range(m):
        nL = L[i:]
        pos,piv,ip = nL[0]
        newpos,newpiv,j = min(nL)
        if ip == j :
            pass
        else :
            nLi = newpos,newpiv,ip
            nLj = pos,piv,j
            A = ope1(A,ip,j)
            B = ope1(B,ip,j)
            L[i] = nLi
            L[j] = nLj
    return A,B

def invertmatrix(A,Id,zero,one):
    #TODO : fix for non square matrix
    m = len(A) #nb of rows
    #n = len(A[0]) #nb col
    B = Id.copy()
    C = Id.copy()
    count = 0
    while not equal(A,C) and not count == 100 :
        #print 'A', A
        #print 'B', B
        count = count+1
        A,B = sortmat(A,B,zero)
        pivotl = pivotlist(A,zero)
        if pivotl[-1][1] == zero or pivotl[-1][1] == None :
            print 'matrix not invertible'
            return A,B,False
        for i in range(m-1,-1,-1):
            pos,piv,ind = pivotl[i]
            if not piv == zero and not piv == None :
                if not piv == one :
                    invpiv = piv**-1

                    A = ope2(A,invpiv,i)
                    B = ope2(B,invpiv,i)
                for j in range(i-1,-1,-1):
                    #print 'A1', A
                    #print 'B1', B
                    v = A[j][pos]
                    #print 'v',v
                    if not v == zero :
                        A = ope3(A,-v,j,i)
                        B = ope3(B,-v,j,i)
    return A,B,True

'''
def prepsys(C,zero):
    pivotl = pivotlist(C,zero)
    r=0 #degrees of liberty
    for pos,piv,i in pivotl :
        if piv == zero or piv == None :
            r=r+1
    l = len(C[0])
    k = l-r
    A = C[0:k,:r]
    B = C[0:k,r:]
'''


def randommat(m,n,rand=None,b=10):
    if random == None :
        def rand():
            return random.randint(0,b)
    A = numpy.zeros((m,n),dtype=object)
    for i in range(m):
        for j in range(n):
            A[i][j] = rand()
    return A

def eye(m,zero,one):
    A = numpy.eye(m,dtype=object)
    for i in range(m):
        for j in range(m):
            if i==j :
                A[i][j] = one
            else :
                A[i][j] = zero
    return A

def equal(A,B):
    m = len(A)
    n = len(A[0])
    if not m == len(B) or not n == len(B[0]):
        return False
    for i in range(m):
        for j in range(n):
            if not A[i][j]==B[i][j]:
                return False
    return True

def inverttest(m):
    '''
    m is the size of the side of the square matrix
    k is the number of tests to be run
    '''
    #t=0
    G = Fp
    zero = G.zero()
    one = G.one()
    Id = eye(m,zero,one)
    rand =G.random

    A = randommat(m,m,rand)
    #print 'matrix initialized'
    #t1 = time.time()
    C,D,b = invertmatrix(A,Id,zero,one)
    #t2 = time.time()
    assert equal(C,Id)
    #print C,D
    assert b == True
    assert equal(numpy.dot(A,D),Id)
    #print 'inversion',i,'done'
    #t = t+t2-t1
    return A,C,D,b


