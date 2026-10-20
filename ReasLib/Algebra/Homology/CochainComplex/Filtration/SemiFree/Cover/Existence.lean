module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Existence of Two-Step Semi-Free Covers

This leaf records the universal construction of an elementary cover of a
differential graded module.  The data owner itself is independent of this
construction and lives in `SemiFree.Cover`.
-/

noncomputable section

universe u

namespace CochainComplex.TwoStepSemiFreeCover

variable {A : Type u} [Ring A]

/-- Lemma 22.20.3 (09KN): every differential graded `A`-module has a two-step semi-free cover
that is degreewise epic and epic on cycles. -/
@[stacks 09KN]
theorem nonempty (M : ModuleCat.DGMod A) : Nonempty (TwoStepSemiFreeCover M) := sorry

end CochainComplex.TwoStepSemiFreeCover
