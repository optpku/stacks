/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphism properties on one-object categories

A submonoid `S : Submonoid R` determines a multiplicative morphism property on the one-object
category `SingleObj R`.  Because composition in `SingleObj R` reverses the displayed
multiplication, categorical left fractions correspond to left Ore data on `S`, while categorical
right fractions correspond to left Ore data on the opposite submonoid `S.op`.

The constructions in this file require only a monoid.  Ring-specific localization and
preadditivity belong to separate layers.
-/

@[expose] public section

open CategoryTheory.MorphismProperty
open OreLocalization

universe u

namespace CategoryTheory.SingleObj

variable {R : Type u} [Monoid R]

/-- The morphism property on `SingleObj R` consisting of the elements of `S : Submonoid R`. -/
@[stacks 0BM1 "multiplicative subsets as morphism properties"]
def submonoidProperty (S : Submonoid R) : MorphismProperty (SingleObj R) :=
  fun _ _ f ↦ f ∈ S

/-- Membership in the one-object morphism property is membership in the original submonoid. -/
@[stacks 0BM1 "membership in the submonoid morphism property", simp]
theorem submonoidProperty.apply_iff (S : Submonoid R)
    {X Y : SingleObj R} (f : X ⟶ Y) :
    submonoidProperty S f ↔ f ∈ S := sorry
/- Proof strategy: unfold `submonoidProperty`. -/

/-- A submonoid defines a multiplicative morphism property on its one-object category. -/
@[stacks 0BM1 "multiplicative submonoid morphism property"]
instance submonoidProperty.isMultiplicative (S : Submonoid R) :
    (submonoidProperty S).IsMultiplicative := sorry
/- Proof strategy: use `S.one_mem` for identities and `S.mul_mem` for composition, reversing the
two factors with `SingleObj.comp_as_mul`. -/

/-- Right calculus of fractions for `S` on `SingleObj R` is left Ore data for the opposite
submonoid `S.op`. -/
@[stacks 0BM1 "right calculus and the opposite Ore set"]
theorem Calculus.right_iff_oreSet (S : Submonoid R) :
    (submonoidProperty S).HasRightCalculusOfFractions ↔
      Nonempty (OreSet S.op) := sorry
/- Proof strategy: apply `OreLocalization.nonempty_oreSet_iff` to `S.op`, remove `op`/`unop`, and
use `SingleObj.comp_as_mul`; reversing multiplication identifies its Ore equations with the
square-completion and extension fields of `HasRightCalculusOfFractions`. -/

/-- Left calculus of fractions for `S` on `SingleObj R` is equivalent to left Ore data on `S`. -/
@[stacks 0BM1 "left calculus and the Ore set"]
theorem Calculus.left_iff_oreSet (S : Submonoid R) :
    (submonoidProperty S).HasLeftCalculusOfFractions ↔
      Nonempty (OreSet S) := sorry
/- Proof strategy: rewrite `OreLocalization.nonempty_oreSet_iff` and
`SingleObj.comp_as_mul`; the Ore square and right-cancellation clauses are exactly the
`exists_leftFraction` and `ext` fields. -/

/-- Right calculus of fractions on `SingleObj R` is equivalent to the explicit right denominator
conditions on a submonoid. -/
@[stacks 0BM1 "right calculus and right denominator conditions"]
theorem Calculus.right_iff_denominator
    (S : Submonoid R) :
    (submonoidProperty S).HasRightCalculusOfFractions ↔
      (∀ (r : R) (s : S), ∃ (r' : R) (s' : S), r * s' = s * r') ∧
        ∀ (r₁ r₂ : R) (s : S), s * r₁ = s * r₂ →
          ∃ s' : S, r₁ * s' = r₂ * s' := sorry
/- Proof strategy: unfold `HasRightCalculusOfFractions` and rewrite composition using
`SingleObj.comp_as_mul`. Its fraction-completion and extension fields give the two displayed
conditions, and the same translations define the converse instance. -/

/-- Left calculus of fractions on `SingleObj R` is equivalent to the explicit left denominator
conditions on a submonoid. -/
@[stacks 0BM1 "left calculus and left denominator conditions"]
theorem Calculus.left_iff_denominator
    (S : Submonoid R) :
    (submonoidProperty S).HasLeftCalculusOfFractions ↔
      (∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s →
          ∃ s' : S, s' * r₁ = s' * r₂) ∧
        ∀ (r : R) (s : S), ∃ (r' : R) (s' : S), s' * r = r' * s := sorry
/- Proof strategy: combine `Calculus.left_iff_oreSet` with
`OreLocalization.nonempty_oreSet_iff`; equivalently translate the calculus fields directly using
`SingleObj.comp_as_mul`. -/

/-- A left Ore set supplies the canonical left calculus of fractions on its one-object category. -/
@[stacks 0BM1 "left Ore sets give left calculi of fractions"]
instance submonoidProperty.hasLeftCalculus
    (S : Submonoid R) [OreSet S] :
    (submonoidProperty S).HasLeftCalculusOfFractions := sorry
/- Proof strategy: use `OreSet.oreNum`, `OreSet.oreDenom`, and `OreSet.ore_eq` for fraction
completion, and `OreSet.ore_right_cancel` for extension. -/

/-- Left Ore data on the opposite submonoid supplies the canonical right calculus of fractions on
the original one-object category. -/
@[stacks 0BM1 "opposite left Ore sets give right calculi of fractions"]
instance submonoidProperty.hasRightCalculus
    (S : Submonoid R) [OreSet S.op] :
    (submonoidProperty S).HasRightCalculusOfFractions := sorry
/- Proof strategy: transport the `OreSet S.op` witnesses across `MulOpposite.op` and `unop`, then
use `SingleObj.comp_as_mul`. -/

end CategoryTheory.SingleObj
