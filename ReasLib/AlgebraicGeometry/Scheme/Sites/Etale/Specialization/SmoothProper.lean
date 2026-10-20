module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity.LocallyConstant

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a smooth proper morphism and a locally constant abelian étale sheaf with
prime-to-characteristic torsion geometric stalks, specialization on geometric stalks
of the derived direct image is an isomorphism. -/
theorem isIso_derivedPushforward_specializationMap_of_locallyConstant
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (F : EtaleVanishingCycles.Coefficients X) [Sheaf.IsLocallyConstant F]
    (hF : geometricStalk_isPrimeToCharTorsion F) :
    IsIso (derivedPushforward_specializationMap f s t point point_over
      (etaleSheafInDegreeZero F)) := sorry

/-- Prime-to-characteristic torsion supplied through `Fact` makes geometric-stalk
specialization of a smooth proper derived direct image invertible for locally
constant abelian étale coefficients. -/
instance isIso_derivedPushforward_specializationMap_of_locallyConstant_of_fact
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (s t : GeometricPoint S)
    (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (F : EtaleVanishingCycles.Coefficients X) [Sheaf.IsLocallyConstant F]
    [Fact (geometricStalk_isPrimeToCharTorsion F)] :
    IsIso (derivedPushforward_specializationMap f s t point point_over
      (etaleSheafInDegreeZero F)) :=
  isIso_derivedPushforward_specializationMap_of_locallyConstant f s t point point_over F Fact.out

end AlgebraicGeometry.Scheme.Etale
