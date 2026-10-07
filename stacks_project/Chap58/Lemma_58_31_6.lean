module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.TameNormalization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Lemma 58.31.6 (1) -/
@[stacks 0EYH] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.isFiniteLocallyFree_fromRelativeNormalization :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y),
      IsFiniteLocallyFree (fromRelativeNormalization i Y))

/- Lemma 58.31.6 (2) -/
@[stacks 0EYH] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.iso_pullback_fromRelativeNormalization :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y),
      Nonempty
        ((Over.mk
            (pullback.snd (fromRelativeNormalization i Y) (closedImmersionComplement i).ι) :
            Over (closedImmersionComplement i).toScheme) ≅
          Over.mk Y.hom))

/- Lemma 58.31.6 (3) -/
@[stacks 0EYH] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.isEffectiveCartierDivisor_reducedPreimageι :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y),
      IsEffectiveCartierDivisor (reducedPreimageι i Y))

/- Lemma 58.31.6 (4) -/
@[stacks 0EYH] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.regular_reducedPreimage :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y),
      Scheme.Regular (reducedPreimage i Y))

/- Lemma 58.31.6 (5) -/
@[stacks 0EYH] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.exists_etaleLocal_sigma_standardRootCover_of_normalization :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y),
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
                    eU.inv))))

end AlgebraicGeometry.Scheme.FiniteEtale
