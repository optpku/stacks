/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.TameNormalization.Valuative
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.FiniteEtale

/- Lemma 58.31.7 (1) -/
@[stacks 0EYI] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.exists_lift_etaleAlongImage :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
      (t : Spec (CommRingCat.of R) ⟶ X)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y)
      (ht : Nonempty
        ((Over.mk (pullback.snd i t) : Over (Spec (CommRingCat.of R))) ≅
          Over.mk
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) :
              Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
                Spec (CommRingCat.of R))))
      (h_lift : ∃ g : Spec (CommRingCat.of K) ⟶ Y.left,
        g ≫ compositeToX i Y =
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t),
      ∃ t' : Spec (CommRingCat.of R) ⟶ relativeNormalization i Y,
        t' ≫ fromRelativeNormalization i Y = t ∧
          ∀ p : Spec (CommRingCat.of R),
            (fromRelativeNormalization i Y).EtaleAt (t'.base p))

/- Lemma 58.31.7 (2) -/
@[stacks 0EYI] #check
  (AlgebraicGeometry.Scheme.FiniteEtale.isFiniteEtale_over_nhds :
    ∀ {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] [Scheme.Regular D]
      (Y : FiniteEtale (closedImmersionComplement i).toScheme)
      {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
      (t : Spec (CommRingCat.of R) ⟶ X)
      (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
        (dense_closedImmersionComplement i) Y)
      (ht : Nonempty
        ((Over.mk (pullback.snd i t) : Over (Spec (CommRingCat.of R))) ≅
          Over.mk
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) :
              Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
                Spec (CommRingCat.of R))))
      (h_generic :
        ∃ n : ℕ,
          Nonempty
            ((Over.mk
                (pullback.snd (compositeToX i Y)
                  (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t)) :
                Over (Spec (CommRingCat.of K))) ≅
              Over.mk (Sigma.desc fun _ : Fin n ↦ 𝟙 (Spec (CommRingCat.of K))))),
      ∃ U : X.Opens, Set.range t.base ⊆ U ∧
        finiteEtaleMorphism (pullback.snd (fromRelativeNormalization i Y) U.ι))

end AlgebraicGeometry.Scheme.FiniteEtale
