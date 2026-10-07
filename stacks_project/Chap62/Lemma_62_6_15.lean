module

public import stacks_project.Chap62.Lemma_62_6_15_Restrict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 62.6.15

Restriction of relative cycles to an open of the source whose complement is
fibrewise of dimension less than `r`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Lemma 62.6.15: if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, `r ≥ 0`, and `U ⊆ X` is open with `dim(X_s \ U_s) < r` for every
`s ∈ S`, then restriction is a bijection `z(X/S, r) → z(U/S, r)`. -/
@[stacks 0H5F]
theorem groupRestrict_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (U : X.Opens) (r : ℕ)
    (hdim : fiberOpenComplementDimensionLT f U r) :
    Function.Bijective (groupRestrict f U r) := sorry

end AlgebraicGeometry.RelativeCycle
