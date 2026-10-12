/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.Submodule
import StacksCheckRecall

@[expose] public section

universe u v

open scoped ENat

namespace Submodule

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (N : Submodule R M)

variable [IsNoetherianRing R] [Module.Finite R M]

/- Exercise 111.12.6 (1): if `(R, m)` is a Noetherian local ring, `M` is a finite
`R`-module with `(2 : ℕ∞) ≤ moduleDepth R M`, and `N ≠ ⊥`, then
`(1 : ℕ∞) ≤ moduleDepth R N`. -/
@[stacks 0CT0]
#check (Submodule.moduleDepth_ge_one (N := N) :
  (2 : ℕ∞) ≤ moduleDepth R M → N ≠ ⊥ → (1 : ℕ∞) ≤ moduleDepth R N)

/- Exercise 111.12.6 (2): if `(R, m)` is a Noetherian local ring, `M` is a finite
`R`-module with `(2 : ℕ∞) ≤ moduleDepth R M`, and `N ≠ ⊥`, then
`moduleDepth R N = 1` if and only if `moduleDepth R (M ⧸ N) = 0`. -/
@[stacks 0CT0]
#check (Submodule.moduleDepth_eq_one_iff (N := N) :
  (2 : ℕ∞) ≤ moduleDepth R M → N ≠ ⊥ →
    (moduleDepth R N = 1 ↔ moduleDepth R (M ⧸ N) = 0))

/- Exercise 111.12.6 (3): the concrete submodule witness
`N' = comap N.mkQ ((maximalIdeal R).primaryComponent (M ⧸ N))` contains `N`. -/
@[stacks 0CT0]
#check (Submodule.le_comapMkQPrimaryComponent (N := N) :
  N ≤ Submodule.comapMkQPrimaryComponent N)

/- Exercise 111.12.6 (4): for the concrete witness
`N' = comap N.mkQ ((maximalIdeal R).primaryComponent (M ⧸ N))`, the finite length
concerns the relative quotient `N' ⧸ N`, represented by `N.submoduleOf N'`. -/
@[stacks 0CT0]
#check (Submodule.length_comapMkQPrimaryComponent_quotient_lt_top (N := N) :
  Module.length R
      (Submodule.comapMkQPrimaryComponent N ⧸
        N.submoduleOf (Submodule.comapMkQPrimaryComponent N)) < ⊤)

/- Exercise 111.12.6 (5): the same concrete witness `N'` has depth at least two,
completing the requested finite-relative-length enlargement. -/
@[stacks 0CT0]
#check (Submodule.moduleDepth_comapMkQPrimaryComponent_ge_two (N := N) :
  (2 : ℕ∞) ≤ moduleDepth R M → N ≠ ⊥ →
    (2 : ℕ∞) ≤ moduleDepth R (Submodule.comapMkQPrimaryComponent N))

end Submodule
