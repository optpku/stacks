module

public import Mathlib.AlgebraicGeometry.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Complement
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Abhyankar
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
variable [IsEffectiveCartierDivisor i] [Scheme.Regular D]
variable (Y : FiniteEtale (closedImmersionComplement i).toScheme)

/-- The structure morphism of `Y` composed with the inclusion of the complement of `D`. -/
abbrev compositeToX : Y.left ⟶ X :=
  Y.hom ≫ (closedImmersionComplement i).ι

/-- The composite of a finite étale morphism with the complement of an effective Cartier divisor
is affine. -/
instance isAffineHom_compositeToX : IsAffineHom (compositeToX i Y) := sorry

/-- The relative normalization of `X` in the finite étale cover `Y` of the complement of `D`. -/
abbrev relativeNormalization : Scheme.{u} :=
  Hom.normalization (compositeToX i Y)

/-- The structure morphism from the relative normalization to `X`. -/
abbrev fromRelativeNormalization : relativeNormalization i Y ⟶ X :=
  Hom.fromNormalization (compositeToX i Y)

/-- The scheme-theoretic inverse image of `D` under the relative normalization morphism. -/
abbrev preimageOfDivisor : Scheme.{u} :=
  pullback i (fromRelativeNormalization i Y)

/-- The reduced scheme underlying the inverse image of `D` under the relative normalization. -/
abbrev reducedPreimage : Scheme.{u} :=
  (preimageOfDivisor i Y).reduction

/-- The canonical closed immersion of the reduced inverse image into the relative normalization. -/
abbrev reducedPreimageι : reducedPreimage i Y ⟶ relativeNormalization i Y :=
  Scheme.reductionι (preimageOfDivisor i Y) ≫ pullback.snd i (fromRelativeNormalization i Y)

/-- The relative normalization morphism is finite locally free under codimension-one tameness. -/
theorem isFiniteLocallyFree_fromRelativeNormalization
    (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    IsFiniteLocallyFree (fromRelativeNormalization i Y) := sorry

/-- The relative normalization restricts to the original finite étale cover on the divisor
complement. -/
theorem iso_pullback_fromRelativeNormalization
    (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    Nonempty
      ((Over.mk
          (pullback.snd (fromRelativeNormalization i Y) (closedImmersionComplement i).ι) :
          Over (closedImmersionComplement i).toScheme) ≅
        Over.mk Y.hom) := sorry

/-- The reduced inverse image of the divisor is an effective Cartier divisor on the relative
normalization. -/
theorem isEffectiveCartierDivisor_reducedPreimageι
    (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    IsEffectiveCartierDivisor (reducedPreimageι i Y) := sorry

/-- The reduced inverse image of the divisor is a regular scheme. -/
theorem regular_reducedPreimage
    (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    Scheme.Regular (reducedPreimage i Y) := sorry

/-- Étale locally on `X`, the relative normalization is a finite coproduct of standard root
covers over a Noetherian ring with regular divisor quotient. -/
theorem exists_etaleLocal_sigma_standardRootCover_of_normalization
    (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    ∀ x : X, ∃ U : Scheme.EtaleNeighborhood X x, ∃ (A : Type u) (_ : CommRing A)
      (_ : IsNoetherianRing A),
      ∃ eU : U.toEtale.left ≅ Spec (CommRingCat.of A),
      ∃ f : A, f ∈ nonZeroDivisors A ∧ IsRegularRing (A ⧸ Ideal.span {f}) ∧
        ∃ n : ℕ, ∃ e : Fin n → ℕ,
          (∀ j, 1 ≤ e j ∧ IsUnit ((e j : A))) ∧
          Nonempty
            ((Over.mk
                (pullback.snd (fromRelativeNormalization i Y) U.toEtale.hom) :
                Over U.toEtale.left) ≅
              Over.mk (Sigma.desc (fun j : Fin n ↦
                Spec.map
                  (CommRingCat.ofHom
                    (algebraMap A (DVR.UniformizerRoot.RootRing f (e j)))) ≫
                  eU.inv))) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
