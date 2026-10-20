module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.TameNormalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
variable [IsEffectiveCartierDivisor i] [Scheme.Regular D]
variable (Y : FiniteEtale (closedImmersionComplement i).toScheme)
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
variable (t : Spec (CommRingCat.of R) ⟶ X)

/-- A generic lift to a tame relative normalization extends across a trait meeting the divisor
with multiplicity one, and the normalization morphism is étale along the resulting lift. -/
theorem exists_lift_etaleAlongImage
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
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t) :
    ∃ t' : Spec (CommRingCat.of R) ⟶ relativeNormalization i Y,
      t' ≫ fromRelativeNormalization i Y = t ∧
        ∀ p : Spec (CommRingCat.of R),
          (fromRelativeNormalization i Y).EtaleAt (t'.base p) :=
  sorry

/-- A split generic fiber makes the tame relative normalization finite étale on an open
neighborhood of the image of the trait. -/
theorem isFiniteEtale_over_nhds
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
            Over.mk (Sigma.desc fun _ : Fin n ↦ 𝟙 (Spec (CommRingCat.of K))))) :
    ∃ U : X.Opens, Set.range t.base ⊆ U ∧
      finiteEtaleMorphism (pullback.snd (fromRelativeNormalization i Y) U.ι) :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
