# -*- coding: utf-8 -*-

"""Some format conversion tools.
"""

from base64 import b64encode
from gmpy import mpz
from re import sub
# from gmpy2 import mpz, bit_length, f_divmod_2exp

ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="

b64toOct = {}
i = 0
for key in "ABCDEFGH":
    b64toOct[key] = "0" + str(i)
    i += 1
for key in "IJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=":
    b64toOct[key] = oct(i)[1:]
    i+= 1

#COUNTER = 0

#def crypthash(m):
#       global COUNTER
#       COUNTER += 1
#       print "counting:", COUNTER
#       return sha256(m)

def mpztob64(mpzval):
    """ converts an mpz integer into a base64 string
    """
    # convert to octal string and pad with 0's to have 2k symbols
    # (octal conversion appears to be 3 times faster than binary)
    octal = mpzval.digits(8)
    octal = "0" * (len(octal) % 2) + octal
    # build resulting base64 string
    b64string = ""
    #print "octal: ", octal
    for i in xrange(0, len(octal), 2):
        b64string += ALPHABET[int(octal[i:i+2], 8)]
    return b64string

def b64tompz(b64string):
    """ converts a base64 string into an mpz integer
    """
    octal = ""
    for c in b64string:
        octal += b64toOct[c]
    return mpz(octal, 8)

#def mpztob64(n):
#   '''Attempt at more efficient solution, but would require gmpy2 '''
#   l = bit_length(n)
#   s = ""
#   for i in xrange(6*(l/6), -1, -6):
#       v, n = f_divmod_2exp(n, i)
#       s += ALPHABET[v]
#   return s

def captounder(s):
    r = s[0].lower()
    r += sub(r'([A-Z])', lambda pat: '_' + pat.group(1).lower(), s[1:])
    return r

def undertocap(s):
    r = s[0].upper()
    r += sub('_'+r'([a-z])', lambda pat: pat.group(1).upper(), s[1:])
    return r

def binn(x):
    b = bin(x)
    s = b[2:]
    return s

def decompBin(x,d,m):
    '''
    x is an integer
    m is the possible total lenght of x
    d is the length of the words
    '''
    b = binn(x)
    assert len(b)<=m
    if len(b)<m :
        t = '0'*(m-len(b))
        b = t+b
    k = len(b)%d
    if not k == 0 :
        t = '0'*(d-k)
        b = t+b

    tu = ()
    while not b == '' :
        fi = b[:d]
        la = b[d:]
        b = la
        tu = tu+(fi,)
    return tu
