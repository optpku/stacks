module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import stacks_project.Chap84.Lemma_84_8_1_InverseImage

/-!
# Abelian and derived adjunctions for `a_X` on algebraic spaces, ph topology

Abelian direct image `a_{X,*} = ε_{X,*} ⋙ π_{X,*}` at `AddCommGrpCat.{u+1}`, the
canonical derived comparison `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)`, and the `D⁺`
adjunction `a_X⁻¹ ⊣ Ra_{X,*}` along `étale ≤ ph`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

variable {S : Scheme.{u}}

/-- Inverse image `a_X⁻¹` preserves finite limits. -/
instance aInverseImage_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteLimits (etalePiInverseImage X ⋙ epsilonPullback X))

/-- Inverse image `a_X⁻¹` preserves finite colimits. -/
instance aInverseImage_preservesFiniteColimits (X : AlgebraicSpace S) :
    PreservesFiniteColimits (aInverseImage X) :=
  inferInstanceAs
    (PreservesFiniteColimits (etalePiInverseImage X ⋙ epsilonPullback X))

/-- Direct image `ε_{X,*}` on abelian sheaves from the big ph slice to the big étale slice. -/
abbrev epsilonPushforward (X : AlgebraicSpace S) :
    Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb etale_le_ph X

/-- `epsilonPushforward` is the abelian topology-comparison direct image along `etale_le_ph`. -/
theorem epsilonPushforward_eq (X : AlgebraicSpace S) :
    epsilonPushforward X = comparisonTopologyPushforwardAb etale_le_ph X := sorry

/-- The bounded-below right-derived functor of `ε_{X,*}` exists. -/
instance epsilonPushforward_hasRightDerivedFunctor (X : AlgebraicSpace S) :
    (epsilonPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})) := sorry

/-- Direct image `a_{X,*}` on abelian sheaves from `(Spaces/X)_ph` to `X_étale`. -/
def aPushforward (X : AlgebraicSpace S) :
    Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  epsilonPushforward X ⋙ etalePiPushforward X

/-- Direct image `a_{X,*}` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
theorem aPushforward_eq (X : AlgebraicSpace S) :
    aPushforward X = epsilonPushforward X ⋙ etalePiPushforward X := sorry

/-- Direct image `a_{X,*}` is additive. -/
instance aPushforward_additive (X : AlgebraicSpace S) : (aPushforward X).Additive :=
  inferInstanceAs ((epsilonPushforward X ⋙ etalePiPushforward X).Additive)

/-- Sheaf-level adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
def aAdjunction (X : AlgebraicSpace S) : aInverseImage X ⊣ aPushforward X :=
  (etalePiAdjunction X).comp
    (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_ph X)

/-- Sheaf-level `a_X⁻¹ ⊣ a_{X,*}` is the composite of `π_X⁻¹ ⊣ π_{X,*}` with
`ε_X⁻¹ ⊣ ε_{X,*}`. -/
theorem aAdjunction_eq (X : AlgebraicSpace S) :
    aAdjunction X =
      (etalePiAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_ph X) :=
  sorry

/-- The bounded-below right-derived functor of `a_{X,*}` exists. -/
instance aPushforward_hasRightDerivedFunctor (X : AlgebraicSpace S) :
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived inverse image `a_X⁻¹` on `D⁺`. -/
def plusAInverseImage (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left (ExactFunctor.of (aInverseImage X))

/-- Bounded-below derived direct image `Ra_{X,*}` on `D⁺`. -/
def plusAPushforward (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (aPushforward X)

/-- Derived direct image `Ra_{X,*}` is the bounded-below right-derived functor of abelian
`a_{X,*}`. -/
theorem plusAPushforward_eq (X : AlgebraicSpace S) :
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X) := sorry

/-- Bounded-below derived adjunction `a_X⁻¹ ⊣ Ra_{X,*}` on `D⁺`. -/
def plusAAdjunction (X : AlgebraicSpace S) :
    plusAInverseImage X ⊣ plusAPushforward X :=
  Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
    (aPushforward X) (aAdjunction X)

/-- The `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}` is the exact-left bounded-below derived adjunction of
abelian `a_X⁻¹ ⊣ a_{X,*}`. -/
theorem plusAAdjunction_eq (X : AlgebraicSpace S) :
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseImage X))
        (aPushforward X) (aAdjunction X) := sorry

/-- Bounded-below derived inverse image `π_X⁻¹` on `D⁺`. -/
abbrev piInverseImagePlus (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (ExactFunctor.of (etalePiInverseImage X))

/-- Bounded-below derived inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on `D⁺`. -/
abbrev aInverseAbPlus (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}) :=
  piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_ph X

/-- Derived inverse image `a_X⁻¹` is the composite of derived `π_X⁻¹` with topology-comparison
inverse image along `etale_le_ph`. -/
theorem aInverseAbPlus_eq (X : AlgebraicSpace S) :
    aInverseAbPlus X =
      piInverseImagePlus X ⋙ Derived.Plus.pullback etale_le_ph X := sorry

/-- The canonical derived comparison map `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)`. -/
def piInverseDerivedUnit (X : AlgebraicSpace S)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (piInverseImagePlus X).obj K ⟶
      (Derived.Plus.pushforward etale_le_ph X).obj ((aInverseAbPlus X).obj K) :=
  (Derived.Plus.unit etale_le_ph X).app ((piInverseImagePlus X).obj K)

/-- `piInverseDerivedUnit` is the bounded-below topology-comparison unit at `π_X⁻¹ K`. -/
theorem piInverseDerivedUnit_eq (X : AlgebraicSpace S)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    piInverseDerivedUnit X K =
      (Derived.Plus.unit etale_le_ph X).app ((piInverseImagePlus X).obj K) := sorry

/-- The sheaf-level adjunction unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism on locally torsion
abelian sheaves. -/
theorem aAdjunction_unit_isIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso ((aAdjunction X).unit.app F) := sorry

/-- Higher direct images `R^q a_{X,*} (a_X⁻¹ F)` vanish for `0 < q` on locally torsion abelian
sheaves. -/
theorem aPushforward_rightDerived_aInverseImage_isZero {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) (hq : 0 < q) :
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseImage X).obj F)) := sorry

/-- The exact-derived presentation of `a_X⁻¹` on `D⁺` is isomorphic to the composite
`aInverseAbPlus`. -/
theorem plusAInverseImage_isIsomorphic_aInverseAbPlus (X : AlgebraicSpace S) :
    IsIsomorphic
      (plusAInverseImage X)
      (aInverseAbPlus X) := sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
