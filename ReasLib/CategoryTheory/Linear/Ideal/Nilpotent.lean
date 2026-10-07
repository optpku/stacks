module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Nilpotent ideal actions in a linear category

This file owns the category-level notion that every element of an ideal acts nilpotently on an
object.  The definition is independent of modules, derived categories, and completeness, so it can
also be reused for complexes, graded objects, and other linear categories.
@stack 091W
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Ideal

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- An ideal acts nilpotently on an object when each of its elements induces a nilpotent scalar
endomorphism. -/
@[stacks 091W "nilpotent ideal action on an object"]
def IsNilpotentOn (I : Ideal R) (X : C) : Prop :=
  ∀ r : I, IsNilpotent (End.of ((r : R) • 𝟙 X))

/-- Elementwise power characterization of a nilpotent ideal action. -/
theorem isNilpotentOn_iff (I : Ideal R) (X : C) :
    I.IsNilpotentOn X ↔
      ∀ r ∈ I, ∃ n : ℕ, (r ^ n : R) • 𝟙 X = 0 := sorry

/-- Every element of a nilpotently acting ideal induces a nilpotent scalar endomorphism. -/
theorem IsNilpotentOn.isNilpotent_smul_id {I : Ideal R} {X : C}
    (hX : I.IsNilpotentOn X) {r : R} (hr : r ∈ I) :
    IsNilpotent (End.of (r • 𝟙 X)) := sorry

/-- A nilpotent ideal action supplies a vanishing power for each scalar endomorphism. -/
theorem IsNilpotentOn.exists_pow_smul_id_eq_zero {I : Ideal R} {X : C}
    (hX : I.IsNilpotentOn X) {r : R} (hr : r ∈ I) :
    ∃ n : ℕ, (r ^ n : R) • 𝟙 X = 0 := sorry

/-- Nilpotence of ideal actions is contravariantly monotone in the ideal. -/
theorem IsNilpotentOn.mono {I J : Ideal R} {X : C}
    (hX : J.IsNilpotentOn X) (hIJ : I ≤ J) :
    I.IsNilpotentOn X := sorry

end Ideal
