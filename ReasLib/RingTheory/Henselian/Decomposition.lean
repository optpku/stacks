module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.KrullDimension.Fiber.MinimalPrime

@[expose] public section

universe u

open IsLocalRing Polynomial

namespace HenselianLocalRing

/-- A commutative local ring is henselian exactly when it satisfies the
coprime polynomial lifting, finite local decomposition, positive-dimensional
finite-type remainder, and pointed etale splitting criteria. -/
theorem decompositionTfae (R : Type u) [CommRing R] [IsLocalRing R] :
    List.TFAE
      [ HenselianLocalRing R
      , ∀ f : R[X],
          ∀ g h : (ResidueField R)[X],
            f.map (residue R) = g * h →
            IsCoprime g h →
            ∃ g' h' : R[X],
              f = g' * h' ∧
              g'.map (residue R) = g ∧
              h'.map (residue R) = h
      , ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
          ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u)
            (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
            (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, Module.Finite R (B i)),
            Nonempty (S ≃ₐ[R] (∀ i, B i))
      , ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
          ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u)
            (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
            (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, Module.Finite R (B i))
            (C : Type u) (_ : CommRing C) (_ : Algebra R C),
            Nonempty (S ≃ₐ[R] ((∀ i, B i) × C)) ∧
              Algebra.Fiber.minimalPrimesPositiveDimensional
                (S := C) (IsLocalRing.closedPoint R)
      , ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.Etale R A]
          (n : Ideal A) [n.IsMaximal] [n.LiesOver (maximalIdeal R)],
          Nonempty (ResidueField R ≃ₐ[R] (A ⧸ n)) →
            ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R A')
              (φ : A ≃ₐ[R] R × A'),
              Ideal.map φ.toRingEquiv.toRingHom n =
                Ideal.prod (maximalIdeal R) (⊤ : Ideal A') ]
    := sorry

end HenselianLocalRing
