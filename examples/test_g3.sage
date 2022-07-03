'''
  Computation of sextic CM types (K, Phi) and their reflex (Kr, Phir).
'''


import os.path
import sys
import time


PROJECT_DIR = os.path.abspath(os.path.join(os.getcwd(), os.pardir))
SAGE_DIR = PROJECT_DIR + '/sage'
CMTYPE_DIR = SAGE_DIR + '/CMType'

load (CMTYPE_DIR + '/cmtype.sage')

R.<x> = PolynomialRing(Rationals())
prec = 1000

data = [
 x^6 - 2*x^5 + 5*x^4 - 7*x^3 + 10*x^2 - 8*x + 8,
 x^6 - 3*x^5 + 9*x^4 - 13*x^3 + 15*x^2 - 9*x + 3,
 x^6 - x^5 + 4*x^4 - 3*x^3 + 8*x^2 - 4*x + 8,
 x^6 - 3*x^5 + 10*x^4 - 15*x^3 + 21*x^2 - 14*x + 7]

for f in data:
    K.<a> = NumberField(f)
    #print (K)
    L, K_to_L = K.galois_closure('b', map=True)
    #print(L)

    K0, K0_to_K = TotallyRealSubfield(K)
    
    CMtypesUpto = AllCMtypesUpToEquivalence(K, K_to_L, True)
    #CMtypes = AllCMtypes(K, K_to_L)

    assert len(CMtypesUpto) == 4, "wrong number of equivalent CM types"
    Phi = CMtypesUpto[0]

    Kr, Kr_to_L, Phir = RefelexField(K, Phi, K_to_L)
    #print ("Kr: ", Kr.polynomial())
    
    
    # test of the right number of CM types modulo equivalence
    assert Kr.is_CM() == true, "Kr is not CM field"
    

