'''

    Author: Bogdan Adrian Dina
    Email: bogdan.dina@mail.huji.ac.il
    Institution: Einstein Institute of Mathematics, Jerusalem, Israel
    Description: Basic functionality for the computation of CM fields, see ...
    Prerequisites:
    Citing this code: Please cite the following leioned if this code has been helpful in your research: 
    Bogdan Adrian Dina and Sorina Ionica, Genus 3 hyperelliptic curves with CM via Shimura reciprocity, The Open Book Series 4 (2020), Fourteenth Algorithmic Number Theory Symposium, https://doi.org/10.2140/obs.2020.4.161


'''


import os
import sys
from itertools import combinations
from sage.rings.number_field.number_field import NumberField_absolute

def TotallyRealSubfield(K):

    SubFieldsStructure = [ tuples for tuples in K.subfields(K.degree()//2) if ( tuples[0].is_totally_real() ) ]
    assert len(SubFieldsStructure) == 1, "There is more than one totally real subfield in K."
    
    K0 = SubFieldsStructure[0][0]
    K0_to_K = SubFieldsStructure[0][1]
    
    return K0, K0_to_K 




def AllCMtypes(K, K_to_L):

    assert K == K_to_L.domain(), "Domain of the Morphism is not K."

    # Compute all CM-types  Phi = {phi in Hom(K,L): iota*phi ≠ psi, psi in Phi} and #Phi = deg(K)/2.
    L = K_to_L.codomain()

    tups = list(map(list, combinations(Hom(K,L), K.degree()//2)))
    assert len(tups) == binomial(Hom(K,L).cardinality(), K.degree()//2), "Wrong commbinatorial number of possible CM types."
     
    all_CMtypes = [PhiK for PhiK in tups if IsCMtype(PhiK)]

    return all_CMtypes




def IsCMtype(Phis):
    L = Phis[0].codomain()
    for i in range(0, len(Phis)):
        for j in range(i+1, len(Phis)):
            if ( L.complex_conjugation()*Phis[i] == Phis[j] ):
                return False
    return True



def OneCMtype(K, K_to_L, index=True):
    all_CMtypes = AllCMtypes(K, K_to_L)

    if index:
        # check that the index of in range [0, len(all_CMtypes)]
        assert index < len(all_CMtypes), "index = %s does not correspond to the maximum number of CM types = %s." %(index, len(all_CMtypes))

        return all_CMtypes[index]
    else:
        return all_CMtypes[0]

def IsPrimitiveCMType(PhiK):
    K = PhiK[0].domain()
    L = PhiK[0].codomain()

    # Check that PhiK is a CM type
    PhiKc = [ L.complex_conjugation()*iotaK for iotaK in PhiK ]
    assert len([ iotaK for iotaK in PhiK if iotaK in PhiKc ]) == 0, "PhiK is not a CM type"
    assert len(PhiK) == (K.degree() // 2), "PhiK does not have the right cardinality"
    
    tups = [F for F in  K.subfields() if ( F[0].is_CM() and F[0].degree() != K.degree() )]
    for tup in tups:
        F = tup[0]
        F_to_K = tup[1]
        
        # F --> K --> L, alpha --> alphaK --> alphaL1, alphaL2, ..., alphaL#PhiK
        embs = [ phiK(F_to_K(F.0)) for phiK in PhiK ];

        # erase doubles.
        embs = set(embs)

        # If #embs == [F:Q], then the PhiK is induced by F up to conjugacy. 
        if ( len(embs) == ( int( F.degree() / 2 ) ) ):
            embs = set( list(embs) + [ conjugate(a) for a in embs ] )
            if ( len(embs) == F.degree() ):
                return False
    return True

def IsEquivalentCMType(Phi1, Phi2):
    K = Phi1[0].domain()
    L = Phi1[0].codomain()

    # Check that Phi1,2 is a CM types and comparable
    Phi1c = [ L.complex_conjugation()*iotaK for iotaK in Phi1 ]
    assert len([ iotaK for iotaK in Phi1 if iotaK in Phi1c ]) == 0, "Phi1 is not a CM type"
    assert len(Phi1) == (K.degree() // 2), "Phi1 does not have the right cardinality"
    Phi2c = [ L.complex_conjugation()*iotaK for iotaK in Phi2 ]
    assert len([ iotaK for iotaK in Phi2 if iotaK in Phi2c ]) == 0, "Phi2 is not a CM type"
    assert len(Phi2) == (K.degree() // 2), "Phi2 does not have the right cardinality"
    assert ( ( Phi1[0].domain() == Phi2[0].domain() ) and ( Phi1[0].codomain() == Phi2[0].codomain() ) ), "Not comparable CM types." 
    
    if set(Phi1c) == set(Phi2):
        return True

    return False
 
def AllCMtypesUpToEquivalence(K, K_to_L, primitive = True):

    assert K == K_to_L.domain(), "Domain of the Morphism is not K."

    CMtypes = AllCMtypes(K, K_to_L)

    doubles = []
    for i in range( 0, len(CMtypes) ):
        for j in range( i, len(CMtypes) ):
            if IsEquivalentCMType( CMtypes[i], CMtypes[j] ):
                doubles.append(j)

    CMtypes_upto_eq = [ CMtypes[i] for i in range( 0, len(CMtypes) ) if i not in doubles ]  
    
    assert len(CMtypes_upto_eq) == ( len(CMtypes)//2 ), "There has to be exactly %s non-equivalent CM types." %len( (CMtypes) // 2 )
 
    if primitive:
        PrimitiveCMtypes = [ PhiK for PhiK in CMtypes_upto_eq if IsPrimitiveCMType(PhiK) ]

        # count the number of primitive CM types
        assert len(PrimitiveCMtypes) == ( len(CMtypes_upto_eq) - len([F for F in  K.subfields() if ( F[0].is_CM() and F[0].degree() != K.degree() )]) ), "Wrong calculation of the number of primitive CM types."
        return PrimitiveCMtypes
    else:
        return CMtypes_upto_eq    

def LiftCMtypeToNormalClosure(PhiK,  K_to_L):
    K = K_to_L.domain()
    L = K_to_L.codomain()

    # Check that PhiK is a CM type, and that the domain/codomain is correct.
    PhiKc = [ L.complex_conjugation()*iotaK for iotaK in PhiK ]
    assert len([ iotaK for iotaK in PhiK if iotaK in PhiKc ]) == 0, "PhiK is not a CM type"
    assert len(PhiK) == (K.degree() // 2), "PhiK does not have the right cardinality"
    assert ( ( PhiK[0].domain() == K_to_L.domain() ) and ( PhiK[0].codomain() == K_to_L.codomain() ) ), "CM type does not has domain/codomain in Morphism."

    AutL = [ alphaL for alphaL in L.galois_group() ]
    assert len(AutL) == L.degree(), "L is not Galois"
    L_complex_conj = [phi for phi in AutL if ( phi.as_hom() == L.complex_conjugation() ) ]
    assert len(L_complex_conj) == 1, "More than one complex conjugation on L."
    L_complex_conj = L_complex_conj[0]

        
    PhiL = [ alphaL for alphaL in AutL if alphaL.as_hom()*K_to_L in PhiK ]
    PhiLc = [ L_complex_conj*alphaL for alphaL in PhiL ]
    assert len([ alphaL for alphaL in PhiL if alphaL in PhiLc ]) == 0, "PhiL is not a CM type"
    assert len(PhiL) == (L.degree() // 2), "PhiL does not have the right cardinality"

    return PhiL

def InverseCMtype(PhiL):
    L = PhiL[0].as_hom().codomain()
    Gal_LQ = L.galois_group()
    assert len(Gal_LQ) == L.degree(), "L is not Galois"
    
    AutL = [ alphaL for alphaL in Gal_LQ ]
    assert len(AutL) == L.degree(), "L is not Galois"

    L_complex_conj = [phi for phi in AutL if ( phi.as_hom() == L.complex_conjugation() ) ]
    assert len(L_complex_conj) == 1, "More than one complex conjugation on L."
    L_complex_conj = L_complex_conj[0]

    # check that PhiL is a CM type
    PhiLc = [L_complex_conj*phiL for phiL in PhiL]
    assert len([ iotaL for iotaL in PhiL if iotaL in PhiLc ]) == 0, "PhiL is not a CM type"
    assert len(PhiL) == (L.degree() // 2), "PhiL does not have the right cardinality"
    
    return [phi^(-1) for phi in PhiL]


def GaloisGroupFixCMtype(PhiL):

    L = PhiL[0].as_hom().codomain()
    Gal_LQ = L.galois_group()
    assert len(Gal_LQ.list()) == L.degree(), "L is not Galois"

    L_complex_conj = [phi for phi in Gal_LQ if ( phi.as_hom() == L.complex_conjugation() ) ]
    assert len(L_complex_conj) == 1, "More than one complex conjugation on L."
    L_complex_conj = L_complex_conj[0]


    # Check that PhiL is CMtype
    PhiLc = [L_complex_conj*phiL for phiL in PhiL]
    assert len([ iotaL for iotaL in PhiL if iotaL in PhiLc ]) == 0, "PhiL is not a CM type"
    assert len(PhiL) == (L.degree() // 2), "PhiL does not have the right cardinality"


    corr_counter = len(PhiL)
    H = []

    # Construct H < Gal(L/QQ) s.t. sigma*PhiL = Phil for sigma in H
    for sigma in Gal_LQ:
        for phi in PhiL:
            if ( (sigma * phi) not in set(PhiL) ):
                corr_counter -= 1

        if corr_counter == len(PhiL):
            H.append(sigma)
        corr_counter = len(PhiL)

    HFixingCMtype = Gal_LQ.subgroup(H)

    # Check that HFixingCMtype < Gal(L/QQ)
    assert HFixingCMtype < Gal_LQ, "HFixingCMtype is not subgroup of Galois(L/QQ)"   

    return HFixingCMtype


def ReflexCMtype(PhiLinv, Kr_to_L):

    Kr = Kr_to_L.domain()
    L = Kr_to_L.codomain()    
    
    Gal_LQ = L.galois_group()
    assert len(Gal_LQ.list()) == L.degree(), "L is not Galois"

    L_complex_conj = [phi for phi in Gal_LQ if ( phi.as_hom() == L.complex_conjugation() ) ]
    assert len(L_complex_conj) == 1, "More than one complex conjugation on L."
    L_complex_conj = L_complex_conj[0]

    # Check that PhiL is CMtype
    PhiLinvc = [L_complex_conj*phiLinv for phiLinv in PhiLinv]
    assert len([ iotaL for iotaL in PhiLinv if iotaL in PhiLinvc ]) == 0, "PhiLinv is not a CM type"
    assert len(PhiLinv) == (L.degree() // 2), "PhiL does not have the right cardinality"
    
    # check that the codomain of PhiLinv is equal to the codomain of Morphism Kr_to_L
    assert PhiLinv[0].as_hom().domain() == Kr_to_L.codomain(), "Not equal codomains." 


    # BOGDAN(TODO): Hier erwischen wir das falsche Tripel, da später CMtype ≠ CMtypeRR gilt.
    PhiKr = set([phi.as_hom()*Kr_to_L for phi in PhiLinv])
    PhiKr = list(PhiKr)

    # From the mathematical point of view PhiKr = set([phi*Kr_to_L for phi in PhiLinv if (phi*Kr_to_L in PhiLinv)]).
    #PhiLinvAsHoms = [phi.as_hom() for phi in PhiLinv]
    #PhiKr1 = set([phi*Kr_to_L for phi in PhiLinvAsHoms if (phi*Kr_to_L in PhiLinvAsHoms)]) 
    #print PhiKr1

    # check that PhiKr is a CMtype     
    assert IsCMtype(list(PhiKr)) == True, "PhiKr is not a CM type"
    assert len(PhiKr) == (Kr.degree() // 2), "PhiKr does not have the right cardinality = %s." %len(PhiKr)
    
    # check that the lift of PhiKr to L is equal to PhiLinv
    PhiKrL = LiftCMtypeToNormalClosure(PhiKr, Kr_to_L)
    assert set(PhiKrL) == set(PhiLinv), "PhiKrL is not equal to PhiLinv"

    return PhiKr

def RefelexField(K, CMType, K_to_L):
    assert K == CMType[0].domain(), "Domain of the Morphism is not K."
    assert K == K_to_L.domain(), "Domain of the Morphism is not K."

    CMTypeL = LiftCMtypeToNormalClosure(CMType, K_to_L)
    H = GaloisGroupFixCMtype(CMTypeL)
    Kr, Kr_to_L = H.fixed_field()

    CMTypeLinv = InverseCMtype(CMTypeL)
    CMTypeR = ReflexCMtype(CMTypeLinv, Kr_to_L)
    assert len(CMTypeR) > 0, "Empty CMTypeR."
    
    return Kr, Kr_to_L, CMTypeR  

