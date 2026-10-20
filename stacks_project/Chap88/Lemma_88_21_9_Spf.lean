module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap87.Lemma_87_14_6_PowerStages
public import stacks_project.Chap87.Lemma_87_38_5_Completion

/-!
# Affine Spf morphisms from algebra maps

An `A`-algebra structure on a ring `B` induces a morphism of fppf sheafy
formal spectra
`completionAlongSubspace (V(IB) ↪ Spec(B)) ⟶
completionAlongSubspace (Spec(A ⧸ I) ↪ Spec(A))`, by postcomposition with
`Spec.map (algebraMap A B)`. The power-stage maps
`Spec(B ⧸ (IB) ^ (n + 1)) ⟶ Spec(A ⧸ I ^ (n + 1))` remain as a comparison
bridge, not as the `Spf` morphism itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The affine scheme `Spec(A)` as an algebraic space over `S`. -/
def specOver {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) : AlgebraicSpace S :=
  ofOver (Over.mk hA)

/-- `specOver hA` is `ofOver` of the structure morphism `hA`. -/
theorem specOver_eq {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) :
    specOver hA = ofOver (Over.mk hA) :=
  sorry

/-- The closed immersion `Spec(A ⧸ I) ⟶ Spec(A)` of algebraic spaces over `S`. -/
def closedImmersion {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    specOver (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hA) ⟶
      specOver hA :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl

/-- `closedImmersion hA I` is `ofOverHomMk` of `Spec.map` of `Ideal.Quotient.mk I`. -/
theorem closedImmersion_eq {A : Type u} [CommRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    closedImmersion hA I =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl :=
  sorry

/-- `closedImmersion hA I` is a closed immersion of algebraic spaces. -/
instance instIsClosedImmersion_closedImmersion {A : Type u} [CommRing A]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    AlgebraicSpace.IsClosedImmersion (closedImmersion hA I) :=
  sorry

/-- The morphism `Spec(B) ⟶ Spec(A)` of algebraic spaces over `S` induced by
`algebraMap A B`. -/
def algebraMapOver {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA) ⟶ specOver hA :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) rfl

/-- `algebraMapOver B hA` is `ofOverHomMk` of `Spec.map` of `algebraMap A B`. -/
theorem algebraMapOver_eq {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    algebraMapOver B hA =
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) rfl :=
  sorry

/-- If a Yoneda section of `Spec(B)` fppf-locally factors through a neighbourhood
of `V(IB)`, then its postcomposition with `algebraMapOver B hA` fppf-locally
factors through a neighbourhood of `Spec(A ⧸ I)`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_algebraMap {A : Type u}
    (B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) {U : (Over S)ᵒᵖ}
    {x : (specOver (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)).functorOfPoints.obj U}
    (hx :
      fppfLocallyFactorsThroughNeighbourhood
        (closedImmersion
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B)))
        x) :
    fppfLocallyFactorsThroughNeighbourhood (closedImmersion hA I)
      ((algebraMapOver B hA).app U x) :=
  sorry

/-- The morphism `Spf(B) ⟶ Spf(A)` of fppf sheafy formal spectra induced by
`algebraMap A B`. -/
def spfAdicCompletionMap {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    completionAlongSubspace
        (closedImmersion
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B))) ⟶
      completionAlongSubspace (closedImmersion hA I) where
  app U :=
    ofHom fun x ↦
      ⟨(algebraMapOver B hA).app U x.1,
        fppfLocallyFactorsThroughNeighbourhood_algebraMap B I hA x.2⟩
  naturality := sorry

/-- The underlying section of `spfAdicCompletionMap` is the component of
`algebraMapOver`. -/
theorem spfAdicCompletionMap_app {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S)
    (I : Ideal A) (U : (Over S)ᵒᵖ)
    (x :
      (completionAlongSubspace
          (closedImmersion
            (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
            (I.map (algebraMap A B)))).obj
        U) :
    (completionAlongSubspace.ι (closedImmersion hA I)).app U
        ((spfAdicCompletionMap B hA I).app U x) =
      (algebraMapOver B hA).app U
        ((completionAlongSubspace.ι
            (closedImmersion
              (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
              (I.map (algebraMap A B)))).app
          U x) :=
  sorry

/-- The kernel inequality needed to induce
`A ⧸ I ^ n →+* B ⧸ (I.map (algebraMap A B)) ^ n` from `algebraMap A B`. -/
theorem le_comap_map_pow {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (n : ℕ) :
    I ^ n ≤ ((I.map (algebraMap A B)) ^ n).comap (algebraMap A B) :=
  sorry

/-- The affine stage map
`Spec(B ⧸ (IB) ^ (n + 1)) ⟶ Spec(A ⧸ I ^ (n + 1))` over `S` induced by
`algebraMap A B`. -/
def powerStageMap {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (n : ℕ) {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) :
    powerStage (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
      (I.map (algebraMap A B)) n ⟶
      powerStage hA I n :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap ((I.map (algebraMap A B)) ^ (n + 1))
        (algebraMap A B) (le_comap_map_pow B I (n + 1)))))
    sorry

/-- The underlying scheme morphism of `powerStageMap` is `Spec.map` of
`Ideal.quotientMap` applied to `algebraMap A B`. -/
theorem powerStageMap_left {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (n : ℕ) {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) :
    (powerStageMap B I n hA).left =
      Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap ((I.map (algebraMap A B)) ^ (n + 1))
          (algebraMap A B) (le_comap_map_pow B I (n + 1)))) :=
  sorry

/-- The morphism of power-thickening diagrams induced by `algebraMap A B`. -/
def powerThickeningsMap {A : Type u} (B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    powerThickenings (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
      (I.map (algebraMap A B)) ⟶
      powerThickenings hA I where
  app n := powerStageMap B I n hA
  naturality := sorry

/-- Components of `powerThickeningsMap` are the stage maps `powerStageMap`. -/
theorem powerThickeningsMap_app {A : Type u} (B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] (I : Ideal A) (n : ℕ) {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) :
    (powerThickeningsMap B I hA).app n = powerStageMap B I n hA :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
