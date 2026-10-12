/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Algebraic.LinearIndependent
public import Mathlib.Data.Complex.Basic

@[expose] public section

open scoped Cardinal

universe u

namespace Module.End

/-- A complex endomorphism of a nontrivial module with countable Hamel rank has nonempty spectrum. -/
theorem spectrum_nonempty_of_rank_le_aleph0
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (T : Module.End ℂ V) (h : Module.rank ℂ V ≤ ℵ₀) :
    (spectrum ℂ T).Nonempty := sorry

end Module.End
