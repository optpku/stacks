module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import stacks_project.Chap84.Lemma_84_8_1_InverseImage

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Adjunction

/-! # Compatibility checks for abelian and derived ph adjunctions -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseImage_preservesFiniteLimits :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    PreservesFiniteLimits (aInverseImage X))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseImage_preservesFiniteColimits :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    PreservesFiniteColimits (aInverseImage X))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPushforward :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPushforward_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    epsilonPushforward X = comparisonTopologyPushforwardAb etale_le_ph X)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPushforward_hasRightDerivedFunctor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (epsilonPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aPushforward :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aPushforward_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    aPushforward X = epsilonPushforward X ⋙ etalePiPushforward X)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aPushforward_additive :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (aPushforward X).Additive)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aAdjunction :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    aInverseImage X ⊣ aPushforward X)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aAdjunction_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    aAdjunction X =
      (etalePiAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_ph X))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aPushforward_hasRightDerivedFunctor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAInverseImage :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAPushforward :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    DerivedCategory.Plus (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAPushforward_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAAdjunction :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    plusAInverseImage X ⊣ plusAPushforward X)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAAdjunction_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
        (aPushforward X) (aAdjunction X))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.piInverseImagePlus :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseAbPlus :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseAbPlus_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    aInverseAbPlus X =
      piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_ph X)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.piInverseDerivedUnit :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    (piInverseImagePlus X).obj K ⟶
      (Derived.Plus.pushforward etale_le_ph X).obj ((aInverseAbPlus X).obj K))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.piInverseDerivedUnit_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    piInverseDerivedUnit X K =
      (Derived.Plus.unit etale_le_ph X).app ((piInverseImagePlus X).obj K))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aAdjunction_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion),
    IsIso ((aAdjunction X).unit.app F))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aPushforward_rightDerived_aInverseImage_isZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) (hq : 0 < q),
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseImage X).obj F)))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAInverseImage_isIsomorphic_aInverseAbPlus :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsIsomorphic
      (plusAInverseImage X)
      (aInverseAbPlus X))

end
