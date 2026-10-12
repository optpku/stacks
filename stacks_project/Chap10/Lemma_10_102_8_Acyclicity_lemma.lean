/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.ChainComplex
import StacksCheckRecall

/-!
# Acyclicity lemma

@stack 00N0
-/

@[expose] public section

open scoped ENat

universe u v

namespace ChainComplex

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (C : ChainComplex (ModuleCat.{v} R) ℕ) {e i : ℕ}
variable (hfinite : C.IsTermwiseFinite) (hbounded : C.IsBoundedLE e)
variable (hi : 0 < i) (hie : i ≤ e)
variable (hdepth : ∀ ⦃j⦄, i ≤ j → j ≤ e → (j : ℕ∞) ≤ moduleDepth R (C.X j))
variable (hexactAbove : ∀ ⦃j⦄, i < j → j ≤ e → C.ExactAt j)

@[stacks 00N0]
#check moduleDepth_homology_ge_one C hfinite hbounded hi hie hdepth hexactAbove

end ChainComplex
