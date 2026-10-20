/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Comparison

/-!
# Abelian and derived adjunctions for `a_X` on algebraic spaces

Abelian direct image `a_{X,*} = ε_{X,*} ⋙ π_{X,*}` at `AddCommGrpCat.{u+1}`, the
canonical derived comparison `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)`, and the `D⁺`
adjunction `a_X⁻¹ ⊣ Ra_{X,*}`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

variable {S : Scheme.{u}}

/-- Inverse image `a_X⁻¹` preserves finite limits. -/
instance aInverseAb_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits (aInverseAb X) :=
  inferInstanceAs
    (PreservesFiniteLimits (etalePiInverseImage X ⋙ epsilonPullback X))

/-- Inverse image `a_X⁻¹` preserves finite colimits. -/
instance aInverseAb_preservesFiniteColimits (X : AlgebraicSpace S) :
    PreservesFiniteColimits (aInverseAb X) :=
  inferInstanceAs
    (PreservesFiniteColimits (etalePiInverseImage X ⋙ epsilonPullback X))

/-- Direct image `a_{X,*}` on abelian sheaves from `(Spaces/X)_fppf` to `X_étale`. -/
def aPushforward (X : AlgebraicSpace S) :
    Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  epsilonPushforward X ⋙ etalePiPushforward X

/-- Direct image `a_{X,*}` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
theorem aPushforward_eq (X : AlgebraicSpace S) :
    aPushforward X = epsilonPushforward X ⋙ etalePiPushforward X := rfl

/-- Direct image `a_{X,*}` is additive. -/
instance aPushforward_additive (X : AlgebraicSpace S) : (aPushforward X).Additive :=
  inferInstanceAs ((epsilonPushforward X ⋙ etalePiPushforward X).Additive)

/-- Sheaf-level adjunction `a_X⁻¹ ⊣ a_{X,*}`. -/
def aAdjunction (X : AlgebraicSpace S) : aInverseAb X ⊣ aPushforward X :=
  (etalePiAdjunction X).comp
    (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X)

/-- Sheaf-level `a_X⁻¹ ⊣ a_{X,*}` is the composite of `π_X⁻¹ ⊣ π_{X,*}` with
`ε_X⁻¹ ⊣ ε_{X,*}`. -/
theorem aAdjunction_eq (X : AlgebraicSpace S) :
    aAdjunction X =
      (etalePiAdjunction X).comp
        (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X) := rfl

/-- The bounded-below right-derived functor of `a_{X,*}` exists. -/
instance aPushforward_hasRightDerivedFunctor (X : AlgebraicSpace S) :
    (aPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1})) := sorry

/-- Bounded-below derived direct image `Ra_{X,*}` on `D⁺`. -/
def plusAPushforward (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (aPushforward X)

/-- Derived direct image `Ra_{X,*}` is the bounded-below right-derived functor of abelian
`a_{X,*}`. -/
theorem plusAPushforward_eq (X : AlgebraicSpace S) :
    plusAPushforward X = Adjunction.Derived.Plus.right (aPushforward X) := rfl

/-- Bounded-below derived adjunction `a_X⁻¹ ⊣ Ra_{X,*}` on `D⁺`. -/
def plusAAdjunction (X : AlgebraicSpace S) :
    Adjunction.Derived.Plus.left (ExactFunctor.of (aInverseAb X)) ⊣ plusAPushforward X :=
  Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseAb X))
    (aPushforward X) (aAdjunction X)

/-- The `D⁺` adjunction `a_X⁻¹ ⊣ Ra_{X,*}` is the exact-left bounded-below derived adjunction of
abelian `a_X⁻¹ ⊣ a_{X,*}`. -/
theorem plusAAdjunction_eq (X : AlgebraicSpace S) :
    plusAAdjunction X =
      Adjunction.Derived.Plus.adjunction (ExactFunctor.of (aInverseAb X))
        (aPushforward X) (aAdjunction X) := rfl

/-- The canonical derived comparison map `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)`. -/
def piInverseDerivedUnit (X : AlgebraicSpace S)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (piInverseImagePlus X).obj K ⟶
      (Derived.Plus.pushforward etale_le_fppf X).obj ((aInverseAbPlus X).obj K) :=
  (Derived.Plus.unit etale_le_fppf X).app ((piInverseImagePlus X).obj K)

/-- `piInverseDerivedUnit` is the bounded-below topology-comparison unit at `π_X⁻¹ K`. -/
theorem piInverseDerivedUnit_eq (X : AlgebraicSpace S)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    piInverseDerivedUnit X K =
      (Derived.Plus.unit etale_le_fppf X).app ((piInverseImagePlus X).obj K) := rfl

/-- The sheaf-level adjunction unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism. -/
instance aAdjunction_unit_isIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IsIso ((aAdjunction X).unit.app F) := sorry

/-- Higher direct images `R^q a_{X,*} (a_X⁻¹ F)` vanish for `0 < q`. -/
theorem aPushforward_rightDerived_aInverseImage_isZero {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    IsZero
      (((aPushforward X).rightDerived q).obj ((aInverseAb X).obj F)) := sorry

/-- The exact-derived presentation of `a_X⁻¹` on `D⁺` is isomorphic to the composite
`aInverseAbPlus`. -/
theorem plusAInverseImage_isIsomorphic_aInverseAbPlus (X : AlgebraicSpace S) :
    IsIsomorphic
      (Adjunction.Derived.Plus.left (ExactFunctor.of (aInverseAb X)))
      (aInverseAbPlus X) := sorry

/-- For `K` in `D⁺(X_étale)`, the canonical map
`π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0DGG]
instance piInverseDerivedUnit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso (piInverseDerivedUnit X K) := sorry

/-- For `K` in `D⁺(X_étale)`, the derived adjunction unit
`K ⟶ Ra_{X,*}(a_X⁻¹ K)` is an isomorphism, where
`a_X : Sh((Spaces/X)_fppf) ⟶ Sh(X_étale)` is the composite `π_X ∘ ε_X`. -/
@[stacks 0DGG]
instance plusAAdjunction_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((plusAAdjunction X).unit.app K) := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
