module

public import stacks_project.Chap62.Definition_62_6_1_Specialization
public import stacks_project.Chap62.Lemma_62_7_3_Equidimensional

/-!
# Equidimensional relative cycles

This file names the additive group `z_equi(X/S, r)` of equidimensional relative
`r`-cycles on a locally finite type morphism `f : X ⟶ S` from a locally
Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.CyclesOnFibers

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)

/-- The zero family of fibrewise `r`-cycles is equidimensional. -/
theorem isEquidimensional_zero : Equidimensional (0 : Family f r) := sorry

/-- The sum of equidimensional families of fibrewise `r`-cycles is equidimensional. -/
theorem isEquidimensional_add {α β : Family f r} (hα : Equidimensional α)
    (hβ : Equidimensional β) : Equidimensional (α + β) := sorry

/-- The negative of an equidimensional family of fibrewise `r`-cycles is
equidimensional. -/
theorem isEquidimensional_neg {α : Family f r} (hα : Equidimensional α) :
    Equidimensional (-α) := sorry

variable [IsLocallyNoetherian S] [LocallyOfFiniteType f]

/-- The abelian group `z_equi(X/S, r)` of equidimensional relative `r`-cycles on
`X / S`: the relative `r`-cycles whose support is contained in a closed
subscheme of relative dimension at most `r`. -/
def equidimensional : AddSubgroup (Family f r) where
  carrier := {α | IsRelative α ∧ Equidimensional α}
  zero_mem' := ⟨isRelative_zero f r, isEquidimensional_zero f r⟩
  add_mem' ha hb := ⟨isRelative_add f r ha.1 hb.1, isEquidimensional_add f r ha.2 hb.2⟩
  neg_mem' ha := ⟨isRelative_neg f r ha.1, isEquidimensional_neg f r ha.2⟩

/-- Membership in `z_equi(X/S, r)` is the conjunction of the relative-cycle
condition and equidimensionality of the family of fibre cycles. -/
theorem mem_equidimensional (α : Family f r) :
    α ∈ equidimensional f r ↔ IsRelative α ∧ Equidimensional α :=
  sorry

/-- A family lies in `z_equi(X/S, r)` if and only if it is a relative `r`-cycle
and its support is contained in a closed subscheme of relative dimension at
most `r`. -/
theorem mem_equidimensional_iff_support (α : Family f r) :
    α ∈ equidimensional f r ↔
      IsRelative α ∧
        ∃ W : X.IdealSheafData,
          support α ⊆ W.support ∧ RelativeDimensionLE (W.subschemeι ≫ f) r :=
  sorry

end AlgebraicGeometry.RelativeCycle

