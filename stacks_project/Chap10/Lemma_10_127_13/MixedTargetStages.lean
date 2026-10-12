/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap10.Lemma_10_127_13.TailApproximation

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- Helper for Lemma 10.127.13: the raw descended-tail comparison to the final local target,
rebuilt with the source ring and the ambient target ring allowed to live in different universes. -/
@[stacks 00QX "mixed-universe descended-tail comparison"]
noncomputable abbrev descendedTailSigmaJointUniverse
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j : Set.Ici i₀) : descendedTailRawStage A₀ i₀ P₀ j →+* S :=
  (algebraMap P S).comp (descendedTailPComp A₀ i₀ P₀ hRalg e j)

/-- Helper for Lemma 10.127.13: the rebuilt mixed-universe raw descended-tail comparisons are
still compatible with the raw tail transition maps. -/
@[stacks 00QX "mixed-universe tail comparison compatibility"]
theorem descended_tail_sigma_joint_universe_comp
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
      (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
        (descendedTailRawMap A₀ i₀ P₀ j k hjk) := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) R :=
    RingHom.toAlgebra
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1)
  letI : Algebra (A₀.RStage k.1) R :=
    RingHom.toAlgebra
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso k.1)
  letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
    Ring.DirectLimit.toLimit_isScalarTower_of_algebraMap_eq
      A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.2 hRalg
  letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage k.1) R :=
    Ring.DirectLimit.toLimit_isScalarTower_of_algebraMap_eq
      A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso k.2 hRalg
  refine RingHom.ext fun x ↦ ?_
  -- Proof comment: both maps transport a tensor from stage `j` to the colimit source `R`,
  -- evaluate it in the descended algebra `P`, and then map to `S`; the tail transition only
  -- changes the right tensor factor, so compatibility reduces to the directed-system relation.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp only [map_zero]
  · intro p r
    simp only [descendedTailSigmaJointUniverse, RingHom.comp_apply]
    have hr :
        Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso k.1
            ((A₀.map j.1 k.1 hjk) r) =
          Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1 r := by
      simp [Ring.DirectLimit.toLimitHom, Ring.DirectLimit.of_f]
    exact (congrArg (algebraMap P S)
      (congrArg e (congrArg (fun z ↦ (p : P₀) ⊗ₜ[A₀.RStage i₀] z) hr))).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 10.127.13: the mixed-universe localized target stage of the descended tail. -/
@[stacks 00QX "mixed-universe localized tail stage"]
abbrev descendedTailSStageJointUniverse
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P) (j : Set.Ici i₀) : Type uR :=
  Localization.AtPrime
    (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (IsLocalRing.maximalIdeal S))

/-- Helper for Lemma 10.127.13: the mixed-universe localized target transition of the descended
tail. -/
@[stacks 00QX "mixed-universe localized tail transition"]
noncomputable abbrev descendedTailTargetMapJointUniverse
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k :=
  Localization.localRingHom
    (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (IsLocalRing.maximalIdeal S))
    (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
      (IsLocalRing.maximalIdeal S))
    (descendedTailRawMap A₀ i₀ P₀ j k hjk)
    ((comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := descendedTailRawMap A₀ i₀ P₀ j k hjk)
      (σA := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (σB := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
      (hσ_raw_comp j k hjk)).symm)

/-- Helper for Lemma 10.127.13: the mixed-universe localized target transition sends a raw-stage
generator to the localization of its raw tensor transition. -/
@[stacks 00QX "mixed-universe localized transition on generators"]
theorem descended_tail_target_map_joint_universe_algebra_map
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (x : descendedTailRawStage A₀ i₀ P₀ j) :
    descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j) x) =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
        (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
        (descendedTailRawMap A₀ i₀ P₀ j k hjk x) := by
  let qTail : (j : Set.Ici i₀) → Ideal (descendedTailRawStage A₀ i₀ P₀ j) := fun j ↦
    Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (IsLocalRing.maximalIdeal S)
  -- Proof comment: after unfolding the canonical localized map between the two prime
  -- localizations, the result is exactly `Localization.localRingHom_to_map`.
  change Localization.localRingHom (qTail j) (qTail k)
        (descendedTailRawMap A₀ i₀ P₀ j k hjk)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := descendedTailRawMap A₀ i₀ P₀ j k hjk)
          (σA := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
          (σB := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
          (hσ_raw_comp j k hjk)).symm)
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (Localization.AtPrime (qTail j)) x) =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
        (Localization.AtPrime (qTail k)) (descendedTailRawMap A₀ i₀ P₀ j k hjk x)
  exact Localization.localRingHom_to_map (I := qTail j) (J := qTail k)
    (f := descendedTailRawMap A₀ i₀ P₀ j k hjk)
    ((comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := descendedTailRawMap A₀ i₀ P₀ j k hjk)
      (σA := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (σB := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
      (hσ_raw_comp j k hjk)).symm) x

/-- Helper for Lemma 10.127.13: after passing to mixed-universe localized tail target stages, the
localized transition on a raw generator multiplied by a source-stage generator agrees with the raw
tensor cancellation map followed by the later localization. -/
private theorem descended_tail_target_map_joint_universe_stage_map_mul_eq_cancel
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (j k : Set.Ici i₀) (hjk : j ≤ k)
    (hcomp : (A₀.map j.1 k.1 hjk).comp (A₀.map i₀ j.1 j.2) = A₀.map i₀ k.1 k.2)
    (x : descendedTailRawStage A₀ i₀ P₀ j) (r' : A₀.RStage k.1) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
    descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j) x) *
      stageMapTail k r' =
    algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
      (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
        j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r')) := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.map j.1 k.1 hjk).toAlgebra
  calc
    descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
            (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j) x) *
        stageMapTail k r' =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
          (descendedTailRawMap A₀ i₀ P₀ j k hjk x) *
        algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
          ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r') := by
        rw [descended_tail_target_map_joint_universe_algebra_map (S := S) A₀ i₀ P₀ hRalg e
          hσ_raw_comp j k hjk x]
        rw [hstageMapTail_apply k r']
        rfl
    _ = algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
          (descendedTailRawMap A₀ i₀ P₀ j k hjk x *
            ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r')) := by
        rw [map_mul]
    _ = algebraMap (descendedTailRawStage A₀ i₀ P₀ k)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
          (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.map a b h) P₀
            j.2 k.2 hjk hcomp (x ⊗ₜ[A₀.RStage j.1] r')) := by
        rw [descendedTailRawTensorCancel_tmul_right A₀ i₀ P₀ j k hjk hcomp x r']

/-- Helper for Lemma 10.127.13: the direct limit of the joint-universe localized target tail. -/
@[stacks 00QX "mixed-universe localized tail limit"]
abbrev descendedTailTargetLimitJointUniverse
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk)) : Type uR :=
  Ring.DirectLimit (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
    (fun j k h ↦ descendedTailTargetMapJointUniverse
      (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)

/-- Helper for Lemma 10.127.13: the canonical map from a joint-universe target stage into its
direct limit. -/
@[stacks 00QX "mixed-universe tail limit inclusion"]
noncomputable abbrev descendedTailTargetOfJointUniverse
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    (j : Set.Ici i₀) :
    descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j →+*
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp :=
  Ring.DirectLimit.of (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
    (fun j k h ↦ descendedTailTargetMapJointUniverse
      (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h) j

/-- Helper for Lemma 10.127.13: the inverse comparison built from the descended presentation sends
raw tail-stage elements to their direct-limit generators for the joint-universe localized target
tail. -/
@[stacks 00QX "mixed-universe tail descent comparison"]
theorem descended_tail_descentPsi_factB_joint_universe
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    [Algebra (A₀.RStage i₀)
      (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)]
    (stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
      descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
    (hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
          ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x))
    (sourceToTargetDirectLimit : R →+*
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    (hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
      sourceToTargetDirectLimit
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso i.1 x) =
      Ring.DirectLimit.of (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
        (fun j k h ↦ descendedTailTargetMapJointUniverse
          (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)
        i (stageMapTail i x))
    (p0Alg : P₀ →ₐ[A₀.RStage i₀]
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    (srcAlg : R →ₐ[A₀.RStage i₀]
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    (hp0Alg : ∀ p : P₀,
      p0Alg p =
        descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp ⟨i₀, le_rfl⟩
          (algebraMap
            (descendedTailRawStage A₀ i₀ P₀ ⟨i₀, le_rfl⟩)
            (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e ⟨i₀, le_rfl⟩)
            ((algebraMap P₀ (descendedTailRawStage A₀ i₀ P₀ ⟨i₀, le_rfl⟩)) p)))
    (hsrcAlg : ∀ r : R, srcAlg r = sourceToTargetDirectLimit r)
    (i : Set.Ici i₀) (w : descendedTailRawStage A₀ i₀ P₀ i) :
    descentPsi e p0Alg srcAlg (descendedTailPComp A₀ i₀ P₀ hRalg e i w) =
      descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e i) w) := sorry

end
