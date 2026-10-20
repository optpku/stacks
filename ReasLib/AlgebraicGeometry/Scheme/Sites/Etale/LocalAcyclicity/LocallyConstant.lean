module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import ReasLib.CategoryTheory.Sites.Sheafification.Abelian

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

/-- A locally acyclic morphism is locally acyclic relative to any locally constant
abelian étale sheaf with prime-to-characteristic torsion geometric stalks,
regarded as a derived object concentrated in degree zero. -/
instance locallyAcyclicRelative_of_locallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Coefficients X)
    [LocallyAcyclic f]
    [Sheaf.IsLocallyConstant F]
    [h_stalk : Fact (geometricStalk_isPrimeToCharTorsion F)] :
    LocallyAcyclicRelative f (etaleSheafInDegreeZero F) :=
  sorry

end AlgebraicGeometry.Scheme
