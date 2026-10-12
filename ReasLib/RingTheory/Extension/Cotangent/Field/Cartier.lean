/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartier equality for finitely generated field extensions

This leaf records the finite-dimensionality of first cotangent homology and
Cartier's Euler-characteristic formula. The corresponding finiteness of
Kaehler differentials is already supplied by `KaehlerDifferential.finite`.

@stack 07E1
-/

@[expose] public section

open scoped KaehlerDifferential

noncomputable section

universe u v

namespace Algebra.H1Cotangent

/-- Lemma 15.34.1 (Cartier equality) (2), tag `07E1`:
for a finitely generated field extension `K / k`, `H1Cotangent k K` is
finite-dimensional over `K`. -/
@[stacks 07E1 "(2)"]
instance finiteDimensional_of_finiteType
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.FiniteType k K] :
    FiniteDimensional K (H1Cotangent k K) := sorry

end Algebra.H1Cotangent

namespace Algebra

/-- Lemma 15.34.1 (Cartier equality) (3), tag `07E1`:
for a finitely generated field extension `K / k`, its transcendence degree is
the Euler characteristic of `H1Cotangent k K ⟶ Ω[K⁄k]`. -/
@[stacks 07E1 "(3)"]
theorem cartier_equality
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.FiniteType k K] :
    Int.ofNat (Cardinal.toNat (trdeg k K)) =
      Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) := sorry

end Algebra

section

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Algebra.FiniteType k K]

/- Lemma 15.34.1 (Cartier equality) (1), tag `07E1`:
the canonical finite-type instance makes `Ω[K⁄k]` finite-dimensional. -/
#synth FiniteDimensional K Ω[K⁄k]

end
