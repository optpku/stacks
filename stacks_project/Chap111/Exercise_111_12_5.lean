/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.PrimaryComponent
public import ReasLib.RingTheory.Depth.Exact
import StacksCheckRecall

@[expose] public section

universe u v

open IsLocalRing
open scoped ENat

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Exercise 111.12.5 (1): writing `K = (maximalIdeal R).primaryComponent M` and
`Q = M ⧸ K` for the kernel and cokernel of the canonical short exact sequence
`0 → K → M → Q → 0` given by `Submodule.subtype K` and `Submodule.mkQ K`,
one has `(1 : ℕ∞) ≤ moduleDepth R Q`. -/
@[stacks 0CSZ] #check
  (Module.moduleDepth_quotient_primaryComponent_ge_one :
    (1 : ℕ∞) ≤ moduleDepth R (M ⧸ (maximalIdeal R).primaryComponent M))

/- Exercise 111.12.5 (2): writing `K = (maximalIdeal R).primaryComponent M` for the
kernel of the canonical short exact sequence `0 → K → M → M ⧸ K → 0` given by
`Submodule.subtype K` and `Submodule.mkQ K`, either `K = ⊥` or
`Module.support R K = {closedPoint R}`. -/
@[stacks 0CSZ] #check
  (Module.primaryComponent_eq_bot_or_support_eq_closedPoint :
    (maximalIdeal R).primaryComponent M = ⊥ ∨
      Module.support R ((maximalIdeal R).primaryComponent M) = {closedPoint R})

/- Exercise 111.12.5 (3): writing `K = (maximalIdeal R).primaryComponent M` for the
kernel of the canonical short exact sequence `0 → K → M → M ⧸ K → 0` given by
`Submodule.subtype K` and `Submodule.mkQ K`, one has
`Module.length R K < ⊤`. -/
@[stacks 0CSZ] #check
  (Module.length_primaryComponent_lt_top :
    Module.length R ((maximalIdeal R).primaryComponent M) < ⊤)

/- The canonical row `0 → K → M → M ⧸ K → 0`, with
`K = (maximalIdeal R).primaryComponent M`, is short exact. -/
#check
  (Submodule.quotientShortExact ((maximalIdeal R).primaryComponent M) :
    (Submodule.quotientShortComplex ((maximalIdeal R).primaryComponent M)).ShortExact)

/- The canonical kernel contains every submodule that is zero or has support equal
to the closed point, giving the maximality described in the hint. -/
#check
  (Module.le_primaryComponent_of_eq_bot_or_support_eq_closedPoint :
    ∀ (N : Submodule R M), (N = ⊥ ∨ Module.support R N = {closedPoint R}) →
      N ≤ (maximalIdeal R).primaryComponent M)
