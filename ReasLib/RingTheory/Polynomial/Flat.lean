/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Flatness of Polynomial Coefficient Maps

This leaf records that changing coefficients preserves flatness for
multivariate polynomial rings.  The primary API is stated for a bare ring
homomorphism, so it does not depend on a chosen algebra presentation; an
algebra-map specialization is provided for the common coefficient-extension
case.
-/

@[expose] public section

universe u v w x

namespace RingHom.Flat

/-- Mapping coefficients along a flat ring homomorphism gives a flat homomorphism of
multivariate polynomial rings. -/
theorem mvPolynomial_map
    {R : Type u} {S : Type v} {σ : Type w}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    (MvPolynomial.map (σ := σ) f).Flat := sorry

end RingHom.Flat

namespace MvPolynomial

/-- Mapping coefficients along a flat algebra homomorphism gives a flat homomorphism of
multivariate polynomial rings. -/
theorem mapAlgHom_flat
    {R : Type u} {A : Type v} {B : Type w} {σ : Type x}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : f.toRingHom.Flat) :
    (mapAlgHom (σ := σ) f).toRingHom.Flat := sorry

/-- The coefficient-extension map on multivariate polynomial rings is flat when the target
algebra is flat over the base ring. -/
theorem mapAlgHom_algebraMap_flat
    {R : Type u} {S : Type v} {σ : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] :
    (mapAlgHom (σ := σ) (Algebra.ofId R S)).toRingHom.Flat := sorry

end MvPolynomial
