module

public import ReasLib.Algebra.Module.Graded.Hilbert
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.Domain

/-!
# Hilbert functions and generic rank

This leaf identifies the generic-rank Hilbert function of a locally finite graded module over a
field with the dimension of each graded piece.
-/

@[expose] public section

universe u v

namespace GradedModule

open CategoryTheory.ModuleCat Module.EulerPoincareFunction

/-- Over a field, generic-rank evaluation of a graded piece is its vector-space dimension. -/
theorem hilbertFunction_genericRank_eq_finrank {k : Type u} {M : Type v} [Field k]
    [AddCommGroup M] [Module k M] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [LocallyFinite ℳ] (n : ℤ) :
    hilbertFunction (CategoryTheory.ModuleCat.K0.Finite.genericRank.{u, v} k) ℳ n =
      (Module.finrank k (ℳ n) : ℤ) := by
  sorry

end GradedModule
