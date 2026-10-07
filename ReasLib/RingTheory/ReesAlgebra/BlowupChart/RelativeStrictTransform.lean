module

public import ReasLib.RingTheory.Flat.Fiber.GeometricallyIntegral
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform

@[expose] public section

open AlgebraicGeometry CommRingCat
open Algebra.TensorProduct
open scoped AffineBlowupChart PrimeSpectrum TensorProduct

noncomputable section

universe u v

namespace AffineBlowupChart

/-- The strict transform of an `S`-module after passing to the affine blowup chart `R[I / a]`:
base change to `S ⊗[R] R[I / a]`, followed by quotienting by the power torsion of the image
of `a`. -/
abbrev relativeStrictTransform
    {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I)
    (M : Type v) [AddCommGroup M] [Module S M] : Type (max u v) :=
  let R' := R[I / a]
  let S' := S ⊗[R] R'
  let T := S' ⊗[S] M
  let a' : S' := Algebra.TensorProduct.includeRight
    (R := R) (A := S) (B := R') (AffineBlowupChart.algebraMap I a a)
  T ⧸ (Ideal.span {a'}).primaryComponent T

namespace RelativeStrictTransform

/-- A finite module of constant rank at the extended base primes away from an element becomes
free of that rank near every extended prime after taking relative strict transforms on the
charts of a suitable finitely generated blowup. -/
@[stacks 0810 "Lemma 38.30.2"]
theorem existsCenterFreeOfRank
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (f : R) (r : ℕ)
    {M : Type v} [AddCommGroup M] [Module S M] [Module.Finite S M]
    [Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    (hM : ∀ (p : PrimeSpectrum R) (_ : f ∉ p.asIdeal),
      Nonempty
        (LocalizedModule.AtPrime (Ideal.map (algebraMap R S) p.asIdeal) M ≃ₗ[Localization.AtPrime
          (Ideal.map (algebraMap R S) p.asIdeal)]
          (Fin r → Localization.AtPrime (Ideal.map (algebraMap R S) p.asIdeal)))) :
    ∃ I : Ideal R,
      I.FG ∧
      V(({f} : Set R)) = V((I : Set R)) ∧
      ∀ a : I,
        let R' := R[I / a]
        let S' := S ⊗[R] R'
        let M' := AffineBlowupChart.relativeStrictTransform S I a M
        ∀ p' : PrimeSpectrum R',
          ∃ g : S',
            g ∉ Ideal.map includeRight.toRingHom p'.asIdeal ∧
            Nonempty
              (LocalizedModule.Away g M' ≃ₗ[Localization.Away g]
                (Fin r → Localization.Away g)) := sorry

end RelativeStrictTransform

end AffineBlowupChart
