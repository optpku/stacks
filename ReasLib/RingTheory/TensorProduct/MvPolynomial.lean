/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Surjective

/-!
# Tensor Base Change of Multivariate Polynomial Maps

This leaf gives the canonical polynomial map obtained by tensoring a
polynomial presentation with a second base algebra.  It keeps the concrete
map, its algebraic square, and its kernel and spectrum consequences together
without attaching them to a particular chapter or a finite variable type.
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace MvPolynomial.AlgHom

-- The right tensor algebra is used only to state the comparison square.  It is not global:
-- Mathlib deliberately avoids the resulting tensor-product instance diamond.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The polynomial map obtained by tensoring a polynomial `R`-algebra map with the `R`-algebra
`T`. -/
@[stacks 00P4 "polynomial-presentation tensor-base-change support"]
noncomputable def baseChange
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) :
    MvPolynomial σ T →ₐ[T] T ⊗[R] S :=
  (Algebra.TensorProduct.map (AlgHom.id T T) π).comp
    (MvPolynomial.algebraTensorAlgEquiv R T).symm.toAlgHom

/-- The tensor base-change map sends a polynomial variable to the tensor of its image with one. -/
@[simp]
theorem baseChange_X
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) (i : σ) :
    baseChange (T := T) π (MvPolynomial.X i) = (1 : T) ⊗ₜ[R] π (MvPolynomial.X i) := sorry

/-- After restricting scalars, tensor base change is the tensor product of `π` with the identity
of the new coefficient ring, transported through the polynomial/tensor equivalence. -/
theorem baseChange_restrictScalars
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) :
    (AlgHom.restrictScalars R (baseChange (T := T) π)) =
      (Algebra.TensorProduct.map (AlgHom.id R T) π).comp
        ((MvPolynomial.algebraTensorAlgEquiv R T).symm.toAlgHom.restrictScalars R) := sorry

/-- The tensor base-change square commutes with the coefficient-extension map on polynomial
rings and the right tensor inclusion. -/
theorem baseChange_comp_map
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) :
    (AlgHom.restrictScalars R (baseChange (T := T) π)).comp
        (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId R T)) =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).comp π := sorry

/-- Tensor base change of a surjective polynomial map is surjective. -/
@[stacks 00P4 "polynomial-presentation tensor-base-change support"]
theorem baseChange_surjective
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) (hπ : Function.Surjective π) :
    Function.Surjective (baseChange (T := T) π) := sorry

/-- The kernel of a surjective polynomial presentation after tensor base change is the extension
of its original kernel along coefficient extension. -/
@[stacks 00P4 "polynomial-presentation tensor-base-change support"]
theorem ker_baseChange
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) (hπ : Function.Surjective π) :
    RingHom.ker (baseChange (T := T) π).toRingHom =
      Ideal.map (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId R T)).toRingHom
        (RingHom.ker π.toRingHom) := sorry

/-- Contracting a prime through the tensor base-change presentation agrees with first
contracting its tensor point and then contracting through the original presentation. -/
@[stacks 00P4 "polynomial-presentation tensor-base-change support"]
theorem comap_baseChange
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S) (q : PrimeSpectrum (T ⊗[R] S)) :
    PrimeSpectrum.comap
        (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId R T)).toRingHom
        (PrimeSpectrum.comap (baseChange (T := T) π).toRingHom q) =
      PrimeSpectrum.comap π.toRingHom
        (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom q) := sorry

/-- The spectrum square for tensor base change after naming the contraction of the tensor point. -/
theorem comap_baseChange_of_eq
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
    (π : MvPolynomial σ R →ₐ[R] S)
    (x : PrimeSpectrum S) (q : PrimeSpectrum (T ⊗[R] S))
    (hq : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom q = x) :
    PrimeSpectrum.comap
        (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId R T)).toRingHom
        (PrimeSpectrum.comap (baseChange (T := T) π).toRingHom q) =
      PrimeSpectrum.comap π.toRingHom x := sorry

/-- For a surjective polynomial presentation, tensor base change preserves the order height of
the corresponding canonical fiber prime.  This is the multivariate-polynomial form of
`Algebra.TensorProduct.comapFiberOrderIso_of_surjective`. -/
@[stacks 00P4 "polynomial-presentation tensor-base-change fiber-prime support"]
theorem baseChange_fiberPrimeAt_orderHeight_eq
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S]
   (π : MvPolynomial σ R →ₐ[R] S) (hπ : Function.Surjective π)
   (q : PrimeSpectrum (T ⊗[R] S)) :
    letI : Algebra (MvPolynomial σ R) (MvPolynomial σ T) :=
      (MvPolynomial.mapAlgHom (Algebra.ofId R T)).toRingHom.toAlgebra
   Order.height
        (fiberPrimeAt (MvPolynomial σ R) (MvPolynomial σ T)
          (PrimeSpectrum.comap (baseChange (T := T) π).toRingHom q)) =
      Order.height (fiberPrimeAt S (T ⊗[R] S) q) := sorry

/-- For a surjective polynomial presentation, flat tensor base change preserves the prime height
defect at corresponding presentation primes. -/
@[stacks 00P4 "polynomial-presentation tensor-base-change prime height-defect support"]
theorem baseChange_primeHeightDefect_eq
    {R : Type u} {T : Type v} {S : Type w} {σ : Type x}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra R S] [Module.Flat R T]
    [IsNoetherianRing (MvPolynomial σ R)] [IsNoetherianRing (MvPolynomial σ T)]
    [IsNoetherianRing S] [IsNoetherianRing (T ⊗[R] S)]
    (π : MvPolynomial σ R →ₐ[R] S) (hπ : Function.Surjective π)
    (q : PrimeSpectrum (T ⊗[R] S)) :
    RingHom.primeHeightDefect (baseChange (T := T) π).toRingHom q =
      RingHom.primeHeightDefect π.toRingHom
        (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom q) := sorry

end MvPolynomial.AlgHom
