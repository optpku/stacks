/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Factoring linear maps through a range

@stack 07JX

This leaf packages the projective lifting property in the range-inclusion
form used by linear-map consumers.
-/

@[expose] public section

universe u v w x

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {N : Type x} [AddCommMonoid N] [Module R N]

/-- A linear map from a projective module factors through every map whose
range contains its range. -/
@[stacks 07JX "projective factorization through a containing range"]
theorem exists_comp_eq_of_range_le (g : P →ₗ[R] N) (f : M →ₗ[R] N)
    (h : g.range ≤ f.range) : ∃ l : P →ₗ[R] M, f.comp l = g := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property f.rangeRestrict
    (g.codRestrict f.range fun y ↦ h (mem_range_self g y)) f.surjective_rangeRestrict
  exact ⟨l, LinearMap.ext fun y ↦
    congrArg Subtype.val (LinearMap.congr_fun hl y)⟩

/-- For a projective source, range inclusion is equivalent to factorization
through the target map. -/
@[stacks 07JX "range inclusion as projective factorization"]
theorem range_le_iff_exists_comp (g : P →ₗ[R] N) (f : M →ₗ[R] N) :
    g.range ≤ f.range ↔ ∃ l : P →ₗ[R] M, f.comp l = g := by
  constructor
  · exact exists_comp_eq_of_range_le g f
  · rintro ⟨l, rfl⟩
    exact range_comp_le_range l f

end LinearMap
