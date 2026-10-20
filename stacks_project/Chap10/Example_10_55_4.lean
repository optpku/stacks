module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.PID
import Mathlib.RingTheory.Polynomial.Content
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.55.4

@stack 00JF
-/

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

variable (k : Type*) [Field k]

/- Example 10.55.4: for a field `k`, the polynomial ring `k[X]` is a principal ideal domain, so
Example 10.55.3 specializes to the canonical equivalence identifying `K₀(k[X])` with `ℤ`. -/
@[stacks 00JF "(1) projective K-group"]
#check (ModuleCat.K0.Projective.genericRankEquiv (Polynomial k) :
  ModuleCat.K0.projective (Polynomial k) ≃+ ℤ)

/- Example 10.55.4: the same specialization identifies `K'_0(k[X])`, modeled here by finitely
generated `k[X]`-modules, with `ℤ`. -/
@[stacks 00JF "(2) finite-module K-group"]
#check (ModuleCat.K0.Finite.genericRankEquiv (Polynomial k) :
  ModuleCat.K0.finite (Polynomial k) ≃+ ℤ)
