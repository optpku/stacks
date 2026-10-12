/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomological dimension of an additive functor

This module packages uniform vanishing and coproduct preservation for the right-derived functors
of an additive functor.  It is independent of any geometric realization of the source category.
-/

open CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v₂ u₂ v₁ u₁

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (F : A ⥤ B) [F.Additive]

/-- The right-derived functors of `F` carry objects satisfying `P` to objects satisfying `Q`
in every degree. -/
@[stacks 0D6U "right-derived functors on object properties"]
def MapsRightDerived (P : ObjectProperty A) (Q : ObjectProperty B) : Prop :=
  ∀ n : ℕ, P ≤ Q.inverseImage (F.rightDerived n)

/-- The right-derived functors of `F` vanish above `d` on objects satisfying `P`. -/
@[stacks 0D6U "relative cohomological dimension"]
def HasCohomologicalDimensionLEOn (P : ObjectProperty A) (d : ℤ) : Prop :=
  ∀ n : ℕ, d < (n : ℤ) → ∀ ⦃X : A⦄, P X → IsZero ((F.rightDerived n).obj X)

/-- Expansion of `MapsRightDerived` into its objectwise condition. -/
@[stacks 0D6U "objectwise higher-direct-image condition"]
theorem mapsRightDerived_iff (P : ObjectProperty A) (Q : ObjectProperty B) :
    F.MapsRightDerived P Q ↔
      ∀ (n : ℕ) ⦃X : A⦄, P X → Q ((F.rightDerived n).obj X) := sorry

/-- Expansion of relative cohomological dimension into objectwise higher-derived vanishing. -/
@[stacks 0D6U "objectwise relative vanishing condition"]
theorem hasCohomologicalDimensionLEOn_iff (P : ObjectProperty A) (d : ℤ) :
    F.HasCohomologicalDimensionLEOn P d ↔
      ∀ (n : ℕ), d < (n : ℤ) → ∀ ⦃X : A⦄,
        P X → IsZero ((F.rightDerived n).obj X) := sorry

/-- The relative right-derived property is monotone in the source and target properties. -/
@[stacks 0D6U "monotonicity of relative right-derived images"]
theorem mapsRightDerived_mono
    {P P' : ObjectProperty A} {Q Q' : ObjectProperty B}
    (hP : P' ≤ P) (hQ : Q ≤ Q')
    (h : F.MapsRightDerived P Q) :
    F.MapsRightDerived P' Q' := sorry

/-- A relative cohomological-dimension bound remains valid after weakening the source property or
raising the bound. -/
@[stacks 0D6U "monotonicity of relative cohomological dimension"]
theorem hasCohomologicalDimensionLEOn_mono
    {P P' : ObjectProperty A} {d d' : ℤ}
    (hP : P' ≤ P) (hd : d ≤ d')
    (h : F.HasCohomologicalDimensionLEOn P d) :
    F.HasCohomologicalDimensionLEOn P' d' := sorry

/-- The right-derived functors of `F` vanish in every natural-number degree strictly above `d`. -/
def HasCohomologicalDimensionLE (d : ℤ) : Prop :=
  ∀ n : ℕ, d < (n : ℤ) → ∀ X : A, IsZero ((F.rightDerived n).obj X)

/-- The right-derived functors of `F` vanish above a uniform finite bound. -/
@[stacks 0F5Z "finite cohomological dimension", stacks 09J7 "finite cohomological dimension"]
def HasFiniteCohomologicalDimension : Prop :=
  ∃ d : ℤ, F.HasCohomologicalDimensionLE d

/-- Every right-derived functor of `F` preserves coproducts indexed in the maximal universe of
the source category. -/
@[stacks 0F5Z "cohomology commutes with coproducts"]
def PreservesCoproductsOfRightDerived : Prop :=
  ∀ (n : ℕ) (I : Type (max u₁ v₁)),
    PreservesColimitsOfShape (Discrete I) (F.rightDerived n)

end CategoryTheory.Functor
