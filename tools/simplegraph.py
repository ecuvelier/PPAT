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

def createCGraph(n):
    Edges = []
    Vertices = []

    counter = n

    while counter > 0:
        if Vertices == []:
            v0 = vertex('0')
            v1 = vertex('1')
            e0 = edge(v0,v1)
            Vertices.append(v0)
            Vertices.append(v1)
            Edges.append(e0)
        else :
            vs = random.choice(Vertices)
            ve = random.choice(Vertices)
            while ve == vertex('0') :
                ve = random.choice(Vertices)
            e = edge(vs,ve)
            prob = random.randint(0,100)
            if vs == ve or e in Edges or prob > 75 :
                l = len(Vertices)
                name = str(l)
                nv = vertex(name)
                ne = edge(vs,nv)
                Vertices.append(nv)
                Edges.append(ne)
            else :
                Edges.append(e)
        counter = counter - 1
    k = len(Vertices)
    M = numpy.zeros((k,k),dtype = object)
    for ed in Edges:
        vs = int(ed.startingvertex.name)
        ve = int(ed.endingvertex.name)
        M[vs,ve] = 1

    return Vertices, Edges, M

class vertex:
    def __init__(self,name):
        self.name = name

    def __eq__(self,other):
        return self.name == other.name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

class edge:
    def __init__(self,startingvertex,endingvertex):
        self.startingvertex = startingvertex
        self.endingvertex = endingvertex

    def __eq__(self,other):
        return self.startingvertex == other.startingvertex and self.endingvertex == other.endingvertex

    def __str__(self):
        return self.startingvertex.name+'-->'+self.endingvertex.name

    def __repr__(self):
        return self.startingvertex.name+'-->'+self.endingvertex.name
