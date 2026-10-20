/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.Bounded
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import ReasLib.RingTheory.Depth

/-!
# Depth and homology of chain complexes

The acyclicity lemma bounds the depth of the last potentially nonexact
homology group from termwise depth bounds on the finite tail of a
bounded-above complex.

@stack 00N0
-/

@[expose] public section

open scoped ENat

universe u v

namespace ChainComplex

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Acyclicity lemma: let `C` be a bounded-above complex of finite modules over
a Noetherian local ring. If `i > 0`, every term from `i` through a bound `e`
has depth at least its degree, and `C` is exact strictly above `i` through
`e`, then the degree-`i` homology has depth at least one. -/
@[stacks 00N0]
theorem moduleDepth_homology_ge_one
    (C : ChainComplex (ModuleCat.{v} R) ℕ) {e i : ℕ}
    (hfinite : C.IsTermwiseFinite) (hbounded : C.IsBoundedLE e)
    (hi : 0 < i) (hie : i ≤ e)
    (hdepth : ∀ ⦃j⦄, i ≤ j → j ≤ e → (j : ℕ∞) ≤ moduleDepth R (C.X j))
    (hexactAbove : ∀ ⦃j⦄, i < j → j ≤ e → C.ExactAt j) :
    (1 : ℕ∞) ≤ moduleDepth R (C.homology i) := sorry

end ChainComplex
