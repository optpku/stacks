/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic

@[expose] public section

/-!
# Exactness modulo a regular element

@stack 00MZ

This leaf records the exactness range retained after quotienting a bounded
finite free complex by a nonzerodivisor in the maximal ideal.
-/

universe u

open IsLocalRing

namespace FiniteFreeComplex

/-- Lemma 10.102.7 (00MZ): if a bounded finite free complex is exact in its
positive degrees, then its termwise quotient by a regular maximal-ideal
element is exact from degree two onward. -/
@[stacks 00MZ]
theorem exact_mod_nonzerodivisor_of_exact
    {R : Type u} [CommRing R] [IsLocalRing R] {e : ℕ}
    (C : _root_.FiniteFreeComplex R e) {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsRegular x)
    (hexact : C.ExactInPositiveDegrees) :
    ∀ j : ℕ, 2 ≤ j → j ≤ e →
      Function.Exact
        (QuotSMulTop.map x (C.toChainComplex.d (j + 1) j).hom)
        (QuotSMulTop.map x (C.toChainComplex.d j (j - 1)).hom) := sorry

end FiniteFreeComplex
