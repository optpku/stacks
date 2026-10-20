module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- Abelian-sheaf relocalization along a scheme morphism preserves injective objects. -/
noncomputable instance relocalization_preservesInjectiveObjects
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}] :
    ((relocalizationFunctor f).sheafPushforwardContinuous
      AddCommGrpCat.{u} T.smallEtaleTopology
      (S.overGrothendieckTopology @Etale)).PreservesInjectiveObjects := sorry

/-- Abelian-sheaf relocalization along a scheme morphism preserves injective objects. -/
theorem relocalization_preservesInjective
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    (I : Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})
    [Injective I] :
    Injective
      (((relocalizationFunctor f).sheafPushforwardContinuous
          AddCommGrpCat.{u} T.smallEtaleTopology
          (S.overGrothendieckTopology @Etale)).obj I) := sorry

/-- Restriction from the big étale site to the small étale site preserves injective objects. -/
theorem relocalization_restriction_preservesInjective
    (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    (I : Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})
    [Injective I] :
    Injective
      (((relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
          AddCommGrpCat.{u} S.smallEtaleTopology
          (S.overGrothendieckTopology @Etale)).obj I) := sorry

/-- Abelian-sheaf relocalization along a scheme morphism preserves K-injective complexes. -/
theorem relocalization_preservesKInjective
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    (I : CochainComplex
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((relocalizationFunctor f).sheafPushforwardContinuous
          AddCommGrpCat.{u} T.smallEtaleTopology
          (S.overGrothendieckTopology @Etale)).mapHomologicalComplex (up ℤ)).obj I) := sorry

/-- Restriction from the big étale site to the small étale site preserves K-injective complexes. -/
theorem relocalization_restriction_preservesKInjective
    (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    (I : CochainComplex
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
          AddCommGrpCat.{u} S.smallEtaleTopology
          (S.overGrothendieckTopology @Etale)).mapHomologicalComplex (up ℤ)).obj I) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig

end
