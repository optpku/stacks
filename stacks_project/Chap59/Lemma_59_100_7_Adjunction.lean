/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap59.Lemma_59_100_6_InverseImage

/-!
# Abelian and derived adjunctions for `a_X`

Abelian direct image `a_{X,*} = ε_{X,*} ⋙ π_{X,*}` at `AddCommGrpCat.{u+1}`, together with the
canonical `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Direct image `π_{X,*}` is additive. -/
instance piPushforward_additive (X : Scheme.{u}) : (piPushforward X).Additive :=
  inferInstanceAs
    ((relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology (etaleTopology.over X)).Additive

/-- Inverse image `a_X⁻¹` preserves finite limits. -/
instance aInverseAb_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (aInverseAb X) :=
  inferInstanceAs
    (PreservesFiniteLimits (piInverseImage X ⋙ epsilonPullback X))

/-- Inverse image `a_X⁻¹` preserves finite colimits. -/
instance aInverseAb_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (aInverseAb X) :=
  inferInstanceAs
    (PreservesFiniteColimits (piInverseImage X ⋙ epsilonPullback X))

/-- Direct image `a_{X,*}` on abelian sheaves from the big fppf slice `(Sch/X)_fppf` to the
small étale site of `X`. -/
def aPushforward (X : Scheme.{u}) :
    Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  epsilonPushforward X ⋙ piPushforward X

/-- Direct image `a_{X,*}` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
theorem aPushforward_eq (X : Scheme.{u}) :
    aPushforward X = epsilonPushforward X ⋙ piPushforward X := sorry

/-- Direct image `a_{X,*}` is additive. -/
instance aPushforward_additive (X : Scheme.{u}) : (aPushforward X).Additive :=
  inferInstanceAs ((epsilonPushforward X ⋙ piPushforward X).Additive)

/-- Sheaf-level adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
def aAdjunction (X : Scheme.{u}) : aInverseAb X ⊣ aPushforward X :=
  (piAdjunction X).comp
    (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X)

/-- Sheaf-level `a_X⁻¹ ⊣ a_{X,*}` is the composite of `π_X⁻¹ ⊣ π_{X,*}` with
`ε_X⁻¹ ⊣ ε_{X,*}`. -/
theorem aAdjunction_eq (X : Scheme.{u}) :
    aAdjunction X =
      (piAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X) :=
  sorry

/-- The bounded-below right-derived functor of `a_{X,*}` exists. -/
instance aPushforward_hasRightDerivedFunctor (X : Scheme.{u}) :
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived direct image `Ra_{X,*}` on `D⁺`. -/
def plusAPushforward (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf (fppfTopology.over X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (aPushforward X)

/-- Derived direct image `Ra_{X,*}` is the bounded-below right-derived functor of abelian
`a_{X,*}`. -/
theorem plusAPushforward_eq (X : Scheme.{u}) :
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X) := sorry

/-- Bounded-below derived adjunction `a_X⁻¹ ⊣ Ra_{X,*}` on `D⁺`. -/
def plusAAdjunction (X : Scheme.{u}) :
    Adjunction.Derived.Plus.left (ExactFunctor.of (aInverseAb X)) ⊣ plusAPushforward X :=
  Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseAb X))
    (aPushforward X) (aAdjunction X)

/-- The `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}` is the exact-left bounded-below derived adjunction of
abelian `a_X⁻¹ ⊣ a_{X,*}`. -/
theorem plusAAdjunction_eq (X : Scheme.{u}) :
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseAb X))
        (aPushforward X) (aAdjunction X) := sorry

/-- The sheaf-level adjunction unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism. -/
theorem aAdjunction_unit_isIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((aAdjunction X).unit.app F) := sorry

/-- Higher direct images `R^q a_{X,*} (a_X⁻¹ F)` vanish for `0 < q`. -/
theorem aPushforward_rightDerived_aInverseImage_isZero {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseAb X).obj F)) := sorry

/-- The exact-derived presentation of `a_X⁻¹` on `D⁺` is isomorphic to the composite
`aInverseAbPlus`. -/
theorem plusAInverseImage_isIsomorphic_aInverseAbPlus (X : Scheme.{u}) :
    IsIsomorphic
      (Adjunction.Derived.Plus.left (ExactFunctor.of (aInverseAb X)))
      (aInverseAbPlus X) := sorry

end AlgebraicGeometry.Scheme.FppfEtale

end

end
