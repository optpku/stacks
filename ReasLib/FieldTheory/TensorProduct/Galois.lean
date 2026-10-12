/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Galois Actions on Tensor Products

This leaf owns the algebraic action obtained by applying an automorphism to the
left factor of a tensor product.  It makes no separability, algebraicity, or
topological assumptions, so later field-theory arguments can specialize it
without recreating the action on either the tensor product or its prime spectrum.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct.Galois

variable {k : Type u} {L : Type v} {K : Type w}
variable [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]

/-- The left-factor action of `Gal(L/k)` on `L ⊗[k] K` by `k`-algebra
automorphisms.  This construction is independent of separability and topology. -/
@[stacks 04KP "left tensor action"]
noncomputable def leftAut :
    Gal(L/k) →* (L ⊗[k] K) ≃ₐ[k] (L ⊗[k] K) where
  toFun σ := Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)
  map_one' := sorry
  map_mul' _ _ := sorry

/-- The semiring action on `L ⊗[k] K` induced by `leftAut`.  It is named rather
than globally installed because a general tensor product can carry several
equally natural factor actions. -/
noncomputable abbrev leftAction :
    MulSemiringAction (Gal(L/k)) (L ⊗[k] K) :=
  MulSemiringAction.compHom (L ⊗[k] K) (leftAut (k := k) (L := L) (K := K))

/-- The pullback of a prime of `L ⊗[k] K` along the inverse of the left-factor
automorphism indexed by `σ`. -/
@[stacks 04KP "prime tensor action"]
noncomputable def primeMap (σ : Gal(L/k)) :
    PrimeSpectrum (L ⊗[k] K) → PrimeSpectrum (L ⊗[k] K) :=
  PrimeSpectrum.comap
    ((leftAut (k := k) (L := L) (K := K) σ).symm.toRingHom)

/-- The action of `Gal(L/k)` on the prime spectrum of `L ⊗[k] K` induced by
the inverse left-factor automorphism. -/
@[stacks 04KP "prime-spectrum action"]
noncomputable abbrev primeAction :
    MulAction (Gal(L/k)) (PrimeSpectrum (L ⊗[k] K)) where
  smul σ := primeMap (k := k) (L := L) (K := K) σ
  one_smul := sorry
  mul_smul := sorry

/-- On ideals, `primeMap σ` is the image under the left-factor automorphism
indexed by `σ`. -/
theorem primeMap_asIdeal (σ : Gal(L/k)) (p : PrimeSpectrum (L ⊗[k] K)) :
    (primeMap (k := k) (L := L) (K := K) σ p).asIdeal =
      Ideal.map ((leftAut (k := k) (L := L) (K := K) σ).toRingEquiv) p.asIdeal := sorry

end Algebra.TensorProduct.Galois
