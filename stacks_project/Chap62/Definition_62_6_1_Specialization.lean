module

public import stacks_project.Chap62.Lemma_62_6_6_Relative

/-!
# The group of relative cycles

This file names the additive group `z(X/S, r)` of relative `r`-cycles on a
locally finite type morphism `f : X ⟶ S` from a locally Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/-- The zero family of fibrewise `r`-cycles is a relative `r`-cycle. -/
theorem isRelative_zero : IsRelative (0 : Family f r) := sorry

/-- The sum of relative `r`-cycles is a relative `r`-cycle. -/
theorem isRelative_add {α β : Family f r} (hα : IsRelative α) (hβ : IsRelative β) :
    IsRelative (α + β) := sorry

/-- The negative of a relative `r`-cycle is a relative `r`-cycle. -/
theorem isRelative_neg {α : Family f r} (hα : IsRelative α) : IsRelative (-α) := sorry

/-- The abelian group `z(X/S, r)` of relative `r`-cycles on `X / S`. -/
def group : AddSubgroup (Family f r) where
  carrier := {α | IsRelative α}
  zero_mem' := isRelative_zero f r
  add_mem' := isRelative_add f r
  neg_mem' := isRelative_neg f r

/-- Membership in `z(X/S, r)` is the relative-cycle condition `IsRelative`. -/
theorem mem_group_iff (α : Family f r) : α ∈ group f r ↔ IsRelative α := sorry

/-- A family lies in `z(X/S, r)` if and only if specialization after every DVR base
change sends the generic-fibre value of `g^*α` to the closed-fibre value. -/
theorem mem_group_iff_specialization (α : Family f r) :
    α ∈ group f r ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (g : Spec (CommRingCat.of R) ⟶ S),
        specialize (pullback.snd f g) r
            (baseChange f g r α (genericPoint (Spec (CommRingCat.of R)))) =
          baseChange f g r α (IsLocalRing.closedPoint R) := sorry

end AlgebraicGeometry.RelativeCycle
