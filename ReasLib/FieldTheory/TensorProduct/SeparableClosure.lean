module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.TensorProduct.Galois
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Galois Actions After Separable Closure

This leaf specializes the neutral left tensor-factor action to a separable
closure.  The action itself is canonical and globally available.  The right
scalar structure and discrete topology are intentionally scoped: they are the
choices needed by the profinite invariant-extension theorem, but are not the
only structures a tensor product may reasonably carry.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.TensorProduct.SeparableClosure.Galois

open scoped Algebra.TensorProduct.Right

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

namespace Action

/-- The canonical action of `Gal(SeparableClosure k/k)` on
`SeparableClosure k ⊗[k] K`, acting on the left tensor factor. -/
@[stacks 04KP "canonical tensor action"]
noncomputable instance ring :
    MulSemiringAction (Gal(SeparableClosure k/k))
      (SeparableClosure k ⊗[k] K) :=
  Algebra.TensorProduct.Galois.leftAction
    (k := k) (L := SeparableClosure k) (K := K)

/-- The canonical action of `Gal(SeparableClosure k/k)` on primes of
`SeparableClosure k ⊗[k] K`. -/
@[stacks 04KP "canonical prime-spectrum action"]
noncomputable instance primes :
    MulAction (Gal(SeparableClosure k/k))
      (PrimeSpectrum (SeparableClosure k ⊗[k] K)) :=
  Algebra.TensorProduct.Galois.primeAction
    (k := k) (L := SeparableClosure k) (K := K)

end Action

/- Re-export the neutral right tensor-factor algebra through the separable-closure scope, so the
specialized continuous-action support is enabled by one scoped import. -/
attribute [scoped instance]
  Algebra.TensorProduct.rightAlgebra

/-- The discrete topology used on `SeparableClosure k ⊗[k] K` by the profinite
invariant-extension argument.  Enable it with
`open scoped Algebra.TensorProduct.SeparableClosure.Galois`. -/
noncomputable scoped instance topology :
    TopologicalSpace (SeparableClosure k ⊗[k] K) :=
  ⊥

/-- The scoped tensor-product topology is discrete. -/
scoped instance discrete : DiscreteTopology (SeparableClosure k ⊗[k] K) := sorry

/-- The left Galois action commutes with the scoped right `K`-scalar action. -/
scoped instance commutes :
    SMulCommClass (Gal(SeparableClosure k/k)) K
      (SeparableClosure k ⊗[k] K) := sorry

/-- The left Galois action is continuous for the Krull topology on the Galois
group and the scoped discrete topology on the tensor product. -/
@[stacks 04KP "continuous tensor action"]
scoped instance continuous :
    ContinuousSMul (Gal(SeparableClosure k/k))
      (SeparableClosure k ⊗[k] K) := sorry

/-- Every fixed point of the left Galois action lies in the scoped right copy
of `K` in `SeparableClosure k ⊗[k] K`.  Together with `commutes`, this gives
the usual fixed-point identification. -/
@[stacks 04KP "invariant tensor extension"]
scoped instance invariant :
    Algebra.IsInvariant K (SeparableClosure k ⊗[k] K)
      (Gal(SeparableClosure k/k)) := sorry

/-- The canonical prime-spectrum action is pullback along the inverse of the
left tensor-factor automorphism. -/
@[stacks 04KP "prime action formula"]
theorem smul_def (σ : Gal(SeparableClosure k/k))
    (p : PrimeSpectrum (SeparableClosure k ⊗[k] K)) :
    σ • p =
      Algebra.TensorProduct.Galois.primeMap
        (k := k) (L := SeparableClosure k) (K := K) σ p := sorry

/-- On prime ideals, the spectrum action is the image under the corresponding
left tensor-factor automorphism. -/
@[stacks 04KP "ideal action formula"]
theorem prime_smul (σ : Gal(SeparableClosure k/k))
    (p : PrimeSpectrum (SeparableClosure k ⊗[k] K)) :
    (σ • p).asIdeal =
      Ideal.map
        ((Algebra.TensorProduct.Galois.leftAut
          (k := k) (L := SeparableClosure k) (K := K) σ).toRingEquiv)
        p.asIdeal := sorry

/-- Lemma 10.47.14 (Tag 04KP): the canonical pretransitivity instance for the
Galois action on primes of `SeparableClosure k ⊗[k] K`. -/
@[stacks 04KP]
instance pretransitive :
    MulAction.IsPretransitive (Gal(SeparableClosure k/k))
      (PrimeSpectrum (SeparableClosure k ⊗[k] K)) := sorry

/-- Lemma 10.47.14 (Tag 04KP), elementwise form: any two primes of
`SeparableClosure k ⊗[k] K` are conjugate under the canonical Galois action. -/
@[stacks 04KP "elementwise form"]
theorem exists_smul_eq (p q : PrimeSpectrum (SeparableClosure k ⊗[k] K)) :
    ∃ σ : Gal(SeparableClosure k/k), σ • p = q := sorry

end Algebra.TensorProduct.SeparableClosure.Galois

section

open scoped Algebra.TensorProduct.SeparableClosure.Galois

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

#synth Algebra K (SeparableClosure k ⊗[k] K)
#synth DiscreteTopology (SeparableClosure k ⊗[k] K)
#synth SMulCommClass (Gal(SeparableClosure k/k)) K (SeparableClosure k ⊗[k] K)
#synth ContinuousSMul (Gal(SeparableClosure k/k)) (SeparableClosure k ⊗[k] K)
#synth Algebra.IsInvariant K (SeparableClosure k ⊗[k] K) (Gal(SeparableClosure k/k))

end
