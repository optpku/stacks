/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.DirectLimit.Tail
public import ReasLib.RingTheory.DirectLimit.Local
public import stacks_project.Chap10.Lemma_10_127_13.MixedTargetStages

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- Helper for Lemma 10.127.13: package the joint-universe localized tail data needed to rebuild
the target colimit without re-expanding the full construction at every call site. -/
@[stacks 00QX "mixed-universe target-tail data"]
structure JointUniverseTargetTailData
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
          (descendedTailRawMap A₀ i₀ P₀ j k hjk)) where
  instTailDirected : IsDirectedOrder (Set.Ici i₀)
  instDirectedSystemRaw :
    DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)
  instDirectedSystemTarget :
    DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)
  stageMapTail : (j : Set.Ici i₀) → A₀.RStage j.1 →+*
    descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j
  hstageMapTail_apply : ∀ (j : Set.Ici i₀) (x : A₀.RStage j.1),
    stageMapTail j x =
      algebraMap (descendedTailRawStage A₀ i₀ P₀ j)
        (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
        ((algebraMap (A₀.RStage j.1) (descendedTailRawStage A₀ i₀ P₀ j)) x)
  hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
    (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
      (descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk).comp
        (stageMapTail j)
  hSourceStage : ∀ (i : Set.Ici i₀) (x : A₀.RStage i.1),
    sourceToTargetDirectLimitOf A₀ i₀
      (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
      stageMapTail (fun {j} {k} hjk ↦ hcommTail hjk)
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
        A₀.colimitIso i.1 x) =
    descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
      (stageMapTail i x)
  htargetColimitToAmbient_comm :
    (tail_target_colimit_to_ambient (S := S)
        (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp
        (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
      f.comp (Ring.DirectLimit.Tail.equivTo (fun i j h ↦ A₀.map i j h)
        i₀ A₀.colimitIso).toRingHom

/-- Helper for Lemma 10.127.13: package the mixed-universe descended tail data before rebuilding
the target colimit. This isolates the source-faithful tail-system construction from the later
owner packaging. -/
@[stacks 00QX "mixed-universe target-tail construction"]
noncomputable def joint_universe_target_tail_data
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (hfg : f = (algebraMap P S).comp (algebraMap R P))
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk)) :
    JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp := by
  let tail : Type uR := Set.Ici i₀
  letI : Preorder tail := inferInstance
  letI : Nonempty tail := inferInstance
  letI : IsDirectedOrder tail := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, le_trans i.2 hik⟩, hik, hjk⟩⟩
  let rawStage : tail → Type uR := descendedTailRawStage A₀ i₀ P₀
  let rawMap : ∀ j k : tail, j ≤ k → rawStage j →+* rawStage k := fun j k hjk ↦
    descendedTailRawMap A₀ i₀ P₀ j k hjk
  let SStage : tail → Type uR := descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e
  let targetMap : ∀ j k : tail, j ≤ k → SStage j →+* SStage k := fun j k hjk ↦
    descendedTailTargetMapJointUniverse
      (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
  have hqTail_comp :
      ∀ j k : tail, ∀ hjk : j ≤ k,
        Ideal.comap (rawMap j k hjk)
            (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
              (IsLocalRing.maximalIdeal S)) =
          Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
            (IsLocalRing.maximalIdeal S) := by
    intro j k hjk
    -- Proof comment: the contracted maximal ideals agree because the later stage comparison to
    -- `S` factors through the earlier one by the raw transition map.
    exact comap_contracted_maximalIdeal_eq_of_comp
      (S := S) (τ := rawMap j k hjk)
      (σA := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
      (σB := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
      (hσ_raw_comp j k hjk)
  have rawMap_id : ∀ j : tail, rawMap j j le_rfl = RingHom.id _ := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: on a fixed stage, the raw transition only acts on the right tensor factor by
    -- the identity map of the source directed system.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.id_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_self (f := fun i j h ↦ A₀.map i j h) y)
    · intro x y hx hy
      simp [map_add, hx, hy]
  have rawMap_comp :
      ∀ i j k : tail, ∀ hij : i ≤ j, ∀ hjk : j ≤ k,
        rawMap i k (le_trans hij hjk) = (rawMap j k hjk).comp (rawMap i j hij) := by
    intro i j k hij hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.map i₀ i.1 i.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    -- Proof comment: the raw tensor transitions compose because they only rewrite the right tensor
    -- factor through the source directed system.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [rawMap]
    · intro x y
      simp only [rawMap, RingHom.comp_apply]
      exact congrArg (fun r ↦ (x : P₀) ⊗ₜ[A₀.RStage i₀] r)
        (DirectedSystem.map_map (f := fun i j h ↦ A₀.map i j h) hij hjk y).symm
    · intro x y hx hy
      simp [map_add, hx, hy]
  letI : DirectedSystem rawStage (fun j k h ↦ rawMap j k h) :=
    { map_self := fun j x ↦ by
        simpa using congrArg (fun g : rawStage j →+* rawStage j ↦ g x) (rawMap_id j)
      map_map := fun {k j i} hij hjk x ↦ by
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : rawStage i →+* rawStage k ↦ g x)
            (rawMap_comp i j k hij hjk)).symm }
  letI : DirectedSystem SStage (fun j k h ↦ targetMap j k h) :=
    { map_self := by
        intro j x
        have hself : targetMap j j le_rfl = RingHom.id (SStage j) := by
          -- Proof comment: once the raw self-transition is the identity, the induced localization
          -- map is the canonical identity localization map.
          change Localization.localRingHom
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                (IsLocalRing.maximalIdeal S))
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                (IsLocalRing.maximalIdeal S))
              (rawMap j j le_rfl)
              ((hqTail_comp j j le_rfl).symm) = RingHom.id (SStage j)
          exact Localization.localRingHom_unique _ _ _ _ fun y ↦ by
            have hy : rawMap j j le_rfl y = y := by
              simpa using congrArg (fun g : rawStage j →+* rawStage j ↦ g y) (rawMap_id j)
            rw [hy]
            rfl
        simpa using congrArg (fun g : SStage j →+* SStage j ↦ g x) hself
      map_map := by
        intro k j i hij hjk x
        have hcomp :
            targetMap i k (le_trans hij hjk) =
              (targetMap j k hjk).comp (targetMap i j hij) := by
          -- Proof comment: the canonical localization maps compose because the underlying raw
          -- tensor transitions compose and the contracted primes match.
          change Localization.localRingHom
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
                (IsLocalRing.maximalIdeal S))
              (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
                (IsLocalRing.maximalIdeal S))
              (rawMap i k (le_trans hij hjk))
              ((hqTail_comp i k (le_trans hij hjk)).symm) =
            (Localization.localRingHom
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                  (IsLocalRing.maximalIdeal S))
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
                  (IsLocalRing.maximalIdeal S))
                (rawMap j k hjk)
                ((hqTail_comp j k hjk).symm)).comp
              (Localization.localRingHom
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
                  (IsLocalRing.maximalIdeal S))
                (Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                  (IsLocalRing.maximalIdeal S))
                (rawMap i j hij)
                ((hqTail_comp i j hij).symm))
          simpa [rawMap_comp i j k hij hjk] using
            (Localization.localRingHom_comp
              (I := Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
                (IsLocalRing.maximalIdeal S))
              (J := Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j)
                (IsLocalRing.maximalIdeal S))
              (K := Ideal.comap (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k)
                (IsLocalRing.maximalIdeal S))
              (f := rawMap i j hij)
              ((hqTail_comp i j hij).symm)
              (g := rawMap j k hjk)
              ((hqTail_comp j k hjk).symm))
        simpa [RingHom.comp_apply] using
          (congrArg (fun g : SStage i →+* SStage k ↦ g x) hcomp).symm }
  let stageMapTail : ∀ j : tail, A₀.RStage j.1 →+* SStage j := fun j ↦ algebraMap _ _
  have hstageMapTail_apply : ∀ (j : tail) (x : A₀.RStage j.1),
      stageMapTail j x =
        algebraMap (rawStage j) (SStage j)
          ((algebraMap (A₀.RStage j.1) (rawStage j)) x) := by
    intro j x
    rfl
  have hcommTail :
      ∀ {j k : tail} (hjk : j ≤ k),
        (stageMapTail k).comp (A₀.map j.1 k.1 hjk) =
          (targetMap j k hjk).comp (stageMapTail j) := by
    intro j k hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.map i₀ k.1 k.2).toAlgebra
    refine RingHom.ext fun x ↦ ?_
    have hraw :
        rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x) =
          (1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.map j.1 k.1 hjk) x) := by
      simp only [rawMap]
      rfl
    -- Proof comment: both composites are the canonical maps from the earlier source stage into
    -- the localization of the later raw tensor stage.
    symm
    calc
      (targetMap j k hjk) ((stageMapTail j) x) =
          algebraMap (rawStage k) (SStage k)
            (rawMap j k hjk ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x)) := by
            rw [show (stageMapTail j) x =
                algebraMap (rawStage j) (SStage j) ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x) from rfl]
            exact descended_tail_target_map_joint_universe_algebra_map
              (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k hjk
              ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x)
      _ = algebraMap (rawStage k) (SStage k)
            ((1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.map j.1 k.1 hjk) x)) := by
            exact congrArg (algebraMap (rawStage k) (SStage k)) hraw
      _ = (stageMapTail k) ((A₀.map j.1 k.1 hjk) x) := rfl
  have hSourceStage : ∀ (i : tail) (x : A₀.RStage i.1),
      sourceToTargetDirectLimitOf A₀ i₀ SStage targetMap stageMapTail
          (fun {j} {k} hjk ↦ hcommTail hjk)
          (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
            A₀.colimitIso i.1 x) =
        descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
          (stageMapTail i x) := by
    intro i x
    -- Proof comment: the source-to-target direct-limit comparison is defined to send each source
    -- stage generator to the corresponding target stage generator.
    exact sourceToTargetDirectLimit_stage_of (A₀ := A₀) (i₀ := i₀)
      (SStage := SStage) (targetMap := targetMap) (stageMapTail := stageMapTail)
      (hcommTail := fun {j} {k} hjk ↦ hcommTail hjk) i x
  let sourceColimitIso :
      Ring.DirectLimit (fun j : tail ↦ A₀.RStage j.1)
        (fun j k h ↦ A₀.map j.1 k.1 h) ≃+* R :=
    Ring.DirectLimit.Tail.equivTo (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso
  have hσ_comp :
      ∀ j : tail,
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j).comp
            (algebraMap (A₀.RStage j.1) (rawStage j)) =
          f.comp
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
              A₀.colimitIso j.1) := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.map i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) R :=
      RingHom.toAlgebra
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.1)
    letI : IsScalarTower (A₀.RStage i₀) (A₀.RStage j.1) R :=
      IsScalarTower.of_algebraMap_eq' (by
        rw [hRalg]
        exact (Ring.DirectLimit.toLimitHom_comp_map A₀.RStage
          (fun i j h ↦ A₀.map i j h) A₀.colimitIso j.2).symm)
    ext x
    -- Proof comment: evaluating the raw tensor-stage comparison on the right tensor generator
    -- recovers the image of `x` in `R`, then in `P`, and finally in `S`.
    simp only [descendedTailSigmaJointUniverse, RingHom.comp_apply, hfg]
    have h1 : (algebraMap (A₀.RStage j.1) (rawStage j)) x =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀] x := rfl
    rw [h1]
    simp only [RingHom.coe_coe]
    exact congrArg (algebraMap P S) (e.commutes ((algebraMap (A₀.RStage j.1) R) x))
  have htargetColimitToAmbient_comm :
      (tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp
          (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)) =
        f.comp sourceColimitIso.toRingHom := by
    apply Ring.DirectLimit.hom_ext
    intro j
    ext x
    -- Proof comment: on each source-stage generator, the ambient colimit map collapses to the raw
    -- stage comparison to `S`, and that comparison is exactly the original map `f`.
    change
      (tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp)
          (descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j
            (stageMapTail j x)) =
        f (sourceColimitIso.toRingHom
          (Ring.DirectLimit.of (fun j : tail ↦ A₀.RStage j.1)
            (fun j k h ↦ A₀.map j.1 k.1 h) j x))
    rw [tail_target_colimit_to_ambient_of (S := S) (G := rawStage) (map := rawMap)
      (σ := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) (hσ := hσ_raw_comp)]
    rw [hstageMapTail_apply j x]
    rw [Localization.localRingHom_to_map]
    have hcompj := congrArg (fun g : A₀.RStage j.1 →+* S ↦ g x) (hσ_comp j)
    change
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j
          ((algebraMap (A₀.RStage j.1) (rawStage j)) x) =
        f ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
          A₀.colimitIso j.1) x) at hcompj
    rw [hcompj]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap, sourceColimitIso,
      Ring.DirectLimit.Tail.equivTo_apply, Ring.DirectLimit.Tail.toFull_of,
      Ring.DirectLimit.toLimitHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    exact congrArg (fun y ↦ f (A₀.colimitIso y))
      (Ring.DirectLimit.Tail.toFull_of (fun i j h ↦ A₀.map i j h) i₀ j x).symm
  exact
    { instTailDirected := inferInstance
      instDirectedSystemRaw := inferInstance
      instDirectedSystemTarget := inferInstance
      stageMapTail := stageMapTail
      hstageMapTail_apply := hstageMapTail_apply
      hcommTail := fun {j} {k} hjk ↦ hcommTail hjk
      hSourceStage := hSourceStage
      htargetColimitToAmbient_comm := htargetColimitToAmbient_comm }

/-- Helper for Lemma 10.127.13: the forward comparison `F` undoes `descentPsi` even when the
ambient target ring lives in a different universe from the descended presentation data. -/
private theorem descentPsi_comp_eq_mixed
    {R₀ P₀ R' P' C : Type uR} {T : Type uS}
    [CommRing R₀] [CommRing P₀] [CommRing R'] [CommRing P'] [CommRing C] [CommRing T]
    [Algebra R₀ P₀] [Algebra R₀ R'] [Algebra R₀ C] [Algebra R' P'] [Algebra P' T]
    (e : P₀ ⊗[R₀] R' ≃ₐ[R'] P') (fP₀ : P₀ →ₐ[R₀] C) (fR : R' →ₐ[R₀] C) (F : C →+* T)
    (hp0 : ∀ p, F (fP₀ p) = algebraMap P' T (e (p ⊗ₜ[R₀] 1)))
    (hsrc : ∀ r, F (fR r) = algebraMap P' T (e ((1 : P₀) ⊗ₜ[R₀] r))) :
    F.comp (descentPsi e fP₀ fR) = algebraMap P' T := by
  have key : ∀ x : P₀ ⊗[R₀] R',
      F (descentPsi e fP₀ fR (e x)) = algebraMap P' T (e x) := by
    intro x
    -- Proof comment: the inverse comparison is multiplicative and is determined by the two tensor
    -- generators, so tensor induction reduces everything to the prescribed formulas on `P₀` and
    -- `R'`.
    induction x using TensorProduct.induction_on with
    | zero =>
        simp
    | tmul p r =>
        rw [descentPsi_apply, map_mul, hp0, hsrc, ← map_mul, ← map_mul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add a b ha hb =>
        simp only [map_add, ha, hb]
  refine RingHom.ext fun p ↦ ?_
  obtain ⟨x, rfl⟩ := e.surjective p
  exact key x

/-- Helper for Lemma 10.127.13: the canonical map from the direct limit of the mixed-universe
localized tail to the ambient local target ring is a local homomorphism. -/
private theorem tail_target_colimit_isLocalHom_mixed
    {Λ : Type w} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type uR) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij)) :
    IsLocalHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) := by
  constructor
  intro x hx
  obtain ⟨i, y, rfl⟩ := Ring.DirectLimit.exists_of x
  rw [tail_target_colimit_to_ambient_of] at hx
  haveI := Localization.isLocalHom_localRingHom
    (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
    (IsLocalRing.maximalIdeal S) (σ i) rfl
  have hy : IsUnit y := isUnit_of_map_unit
    (Localization.localRingHom (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))
      (IsLocalRing.maximalIdeal S) (σ i) rfl) y
    (isUnit_of_map_unit (maxLocalizationCollapse S).toRingEquiv _ hx)
  exact hy.map (Ring.DirectLimit.of
    (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
    (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
      ((comap_contracted_maximalIdeal_eq_of_comp
        (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) i)

/-- Helper for Lemma 10.127.13: a mixed-universe localized tail direct limit is canonically
identified with the ambient local target ring once an inverse comparison map has been built. -/
private theorem tailTargetColimitEquiv_mixed
    {Λ : Type w} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type uR) [∀ i, CommRing (G i)]
    (map : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ map i j h)]
    (σ : (i : Λ) → G i →+* S)
    (hσ : ∀ i j (hij : i ≤ j), σ i = (σ j).comp (map i j hij))
    {P : Type uR} [CommRing P] [Algebra P S]
    (q : Ideal P) [q.IsPrime] [IsLocalization q.primeCompl S]
    (pComp : (i : Λ) → G i →+* P)
    (hpComp : ∀ i, (algebraMap P S).comp (pComp i) = σ i)
    (ψ : P →+* Ring.DirectLimit
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)))
    (hψ : (tail_target_colimit_to_ambient (S := S) G map σ hσ).comp ψ = algebraMap P S)
    (hfactB : ∀ (i : Λ) (w : G i),
      ψ (pComp i w) = Ring.DirectLimit.of
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm))
        i (algebraMap (G i)
          (Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S))) w)) :
    ∃ eTail : Ring.DirectLimit
        (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
        (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
          ((comap_contracted_maximalIdeal_eq_of_comp
            (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) ≃+* S,
      eTail.toRingHom = tail_target_colimit_to_ambient (S := S) G map σ hσ := by
  haveI hDS := localized_contracted_maximalIdeal_directedSystem (S := S) G map σ hσ
  have hlocal : IsLocalHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) :=
    tail_target_colimit_isLocalHom_mixed (S := S) G map σ hσ
  have hunits : ∀ y : q.primeCompl, IsUnit (ψ (y : P)) := by
    intro y
    -- Proof comment: the inverse comparison sends each denominator to a unit because its image in
    -- `S` is already a unit and the ambient colimit map is local.
    apply hlocal.1
    rw [show (tail_target_colimit_to_ambient (S := S) G map σ hσ) (ψ (y : P))
        = algebraMap P S (y : P) from congrArg (fun h : P →+* S ↦ h (y : P)) hψ]
    exact IsLocalization.map_units S y
  let invMap : S →+* Ring.DirectLimit
      (fun i ↦ Localization.AtPrime (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)))
      (fun i j h ↦ Localization.localRingHom _ _ (map i j h)
        ((comap_contracted_maximalIdeal_eq_of_comp
          (S := S) (τ := map i j h) (σA := σ i) (σB := σ j) (hσ i j h)).symm)) :=
    IsLocalization.lift (M := q.primeCompl) hunits
  have hforward : (tail_target_colimit_to_ambient (S := S) G map σ hσ).comp invMap =
      RingHom.id S := by
    apply IsLocalization.ringHom_ext q.primeCompl
    refine RingHom.ext fun x ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [show invMap (algebraMap P S x) = ψ x from IsLocalization.lift_eq hunits x]
    exact congrArg (fun h : P →+* S ↦ h x) hψ
  have hbackward :
      invMap.comp (tail_target_colimit_to_ambient (S := S) G map σ hσ) = RingHom.id _ := by
    apply Ring.DirectLimit.hom_ext
    intro i
    apply IsLocalization.ringHom_ext
      (Ideal.comap (σ i) (IsLocalRing.maximalIdeal S)).primeCompl
    refine RingHom.ext fun w ↦ ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [tail_target_colimit_to_ambient_of (S := S) G map σ hσ, Localization.localRingHom_to_map]
    simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap]
    rw [show σ i w = algebraMap P S (pComp i w) from
      (congrArg (fun h : G i →+* S ↦ h w) (hpComp i)).symm]
    rw [IsLocalization.lift_eq hunits (pComp i w)]
    exact hfactB i w
  -- Proof comment: the lifted inverse map is inverse to the ambient colimit map because both
  -- composites agree on localization generators, hence on the whole localized tail.
  exact ⟨RingEquiv.ofRingHom (tail_target_colimit_to_ambient (S := S) G map σ hσ) invMap
    hforward hbackward, rfl⟩

/-- Helper for Lemma 10.127.13: package only the short descended-comparison inputs needed by the
mixed-universe tail-colimit equivalence, keeping the giant tail bundle out of the application
boundary. -/
private structure JointUniverseTargetColimitInputs
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
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)] where
  instAlgTargetLimit : Algebra (A₀.RStage i₀)
    (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
  p0Alg :
    let _ : Algebra (A₀.RStage i₀)
        (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :=
      instAlgTargetLimit
    P₀ →ₐ[A₀.RStage i₀]
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  srcAlg :
    let _ : Algebra (A₀.RStage i₀)
        (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :=
      instAlgTargetLimit
    R →ₐ[A₀.RStage i₀]
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  psi : P →+*
    descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  hpsi :
    (tail_target_colimit_to_ambient (S := S)
        (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp psi =
      algebraMap P S
  hfactB : ∀ (i : Set.Ici i₀) (w : descendedTailRawStage A₀ i₀ P₀ i),
    psi (descendedTailPComp A₀ i₀ P₀ hRalg e i w) =
      descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e i) w)

/-- Helper for Lemma 10.127.13: from the packaged joint-universe tail bundle, construct the
minimal `p₀`, source, and inverse-comparison maps needed by `tailTargetColimitEquiv_mixed`. -/
private theorem joint_universe_target_colimit_inputs
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (g : R →+* P) (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    (bundle : JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :
    Nonempty (JointUniverseTargetColimitInputs (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) := by
  let C := descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
  let b : Set.Ici i₀ := ⟨i₀, le_rfl⟩
  let src : R →+* C := sourceToTargetDirectLimitOf A₀ i₀
    (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
    (descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp)
    bundle.stageMapTail (fun {j} {k} h ↦ bundle.hcommTail h)
  letI : Algebra (A₀.RStage i₀) C := (src.comp (algebraMap (A₀.RStage i₀) R)).toAlgebra
  let srcAlg : R →ₐ[A₀.RStage i₀] C := { src with commutes' := fun _ ↦ rfl }
  have hbalance (B : Type uR) [CommRing B] [Algebra (A₀.RStage i₀) B]
      (r : A₀.RStage i₀) :
      (algebraMap (A₀.RStage i₀) P₀ r) ⊗ₜ[A₀.RStage i₀] (1 : B) =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀] (algebraMap (A₀.RStage i₀) B r) := by
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul r (1 : P₀) (1 : B))
  -- The base raw stage uses the self-transition algebra and its induced module action.
  letI : Algebra (A₀.RStage i₀) (A₀.RStage i₀) := (A₀.map i₀ i₀ le_rfl).toAlgebra
  letI : Module (A₀.RStage i₀) (A₀.RStage i₀) := Algebra.toModule
  let p0Map : P₀ →+* C :=
    (descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp b).comp
      ((algebraMap (descendedTailRawStage A₀ i₀ P₀ b)
        (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e b)).comp
          (Algebra.TensorProduct.includeLeftRingHom (R := A₀.RStage i₀)))
  have hp0Stage (i : Set.Ici i₀) (p : P₀) :
      letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.map i₀ i.1 i.2).toAlgebra
      p0Map p = descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
        (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
          (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e i)
          (p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i.1))) := by
    letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.map i₀ i.1 i.2).toAlgebra
    symm
    calc
      _ = descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
          (descendedTailTargetMapJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp b i i.2
            (algebraMap (descendedTailRawStage A₀ i₀ P₀ b)
              (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e b)
              (p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i₀)))) := by
        rw [descended_tail_target_map_joint_universe_algebra_map]
        simp only [descendedTailRawMap, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, map_one]
      _ = p0Map p := Ring.DirectLimit.of_f (i := b) (j := i) i.2 _
  let p0Alg : P₀ →ₐ[A₀.RStage i₀] C :=
    { p0Map with
      commutes' := fun r ↦ by
        change p0Map (algebraMap (A₀.RStage i₀) P₀ r) = src (algebraMap (A₀.RStage i₀) R r)
        rw [hp0Stage b, hRalg]
        rw [show src (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h)
            A₀.colimitIso i₀ r) = _ from bundle.hSourceStage b r]
        rw [bundle.hstageMapTail_apply]
        congr 2
        change (algebraMap (A₀.RStage i₀) P₀ r) ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i₀) =
          (1 : P₀) ⊗ₜ[A₀.RStage i₀] r
        have hr : algebraMap (A₀.RStage i₀) (A₀.RStage i₀) r = r :=
          DirectedSystem.map_self (f := fun i j h ↦ A₀.map i j h) r
        exact (hbalance (A₀.RStage i₀) r).trans
          (congrArg (fun x ↦ (1 : P₀) ⊗ₜ[A₀.RStage i₀] x) hr) }
  let psi := descentPsi e p0Alg srcAlg
  have hfactB (i : Set.Ici i₀) (w : descendedTailRawStage A₀ i₀ P₀ i) :
      psi (descendedTailPComp A₀ i₀ P₀ hRalg e i w) =
        descendedTailTargetOfJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp i
          (algebraMap (descendedTailRawStage A₀ i₀ P₀ i)
            (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e i) w) := by
    letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.map i₀ i.1 i.2).toAlgebra
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p r =>
      change descentPsi e p0Alg srcAlg
        (e (p ⊗ₜ[A₀.RStage i₀] (Ring.DirectLimit.toLimitHom A₀.RStage
          (fun i j h ↦ A₀.map i j h) A₀.colimitIso i.1 r))) = _
      rw [descentPsi_apply]
      change p0Map p * src (Ring.DirectLimit.toLimitHom A₀.RStage
        (fun i j h ↦ A₀.map i j h) A₀.colimitIso i.1 r) = _
      rw [hp0Stage i, bundle.hSourceStage, bundle.hstageMapTail_apply]
      change Ring.DirectLimit.of _ _ i (algebraMap _ _ (p ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage i.1))) *
        Ring.DirectLimit.of _ _ i (algebraMap _ _ ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r)) = _
      rw [← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hpsi : (tail_target_colimit_to_ambient (S := S)
      (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
      (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp).comp psi =
        algebraMap P S := by
    apply descentPsi_comp_eq_mixed e p0Alg srcAlg
    · intro p
      change (tail_target_colimit_to_ambient (S := S) _ _ _ _)
        (p0Map p) = _
      rw [hp0Stage b, tail_target_colimit_to_ambient_of, Localization.localRingHom_to_map]
      simp only [RingHom.coe_coe, maxLocalizationCollapse_algebraMap]
      change algebraMap P S (e (p ⊗ₜ[A₀.RStage i₀]
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀ 1))) = _
      rw [map_one]
    · intro r
      have hr := DFunLike.congr_fun bundle.htargetColimitToAmbient_comm
        ((Ring.DirectLimit.Tail.equivTo (fun i j h ↦ A₀.map i j h) i₀ A₀.colimitIso).symm r)
      change (tail_target_colimit_to_ambient (S := S) _ _ _ _) (srcAlg r) = _
      change (tail_target_colimit_to_ambient (S := S) _ _ _ _) (src r) = _
      have hr' : (tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp)
          (src r) = f r := by
        simpa only [src, sourceToTargetDirectLimitOf, RingHom.comp_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          RingEquiv.apply_symm_apply] using hr
      rw [hr', hfg, RingHom.comp_apply, ← hPalg]
      exact congrArg (algebraMap P S) (e.commutes r).symm
  exact ⟨{
    instAlgTargetLimit := inferInstance
    p0Alg := p0Alg
    srcAlg := srcAlg
    psi := psi
    hpsi := hpsi
    hfactB := hfactB }⟩

/-- Helper for Lemma 10.127.13: the packaged mixed-universe target-tail data identifies the
localized target colimit with the ambient local target ring. -/
@[stacks 00QX "mixed-universe target-colimit equivalence"]
theorem joint_universe_target_colimit_equiv_from_bundle
    (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
    {P : Type uR} [CommRing P] [Algebra R P] [Algebra P S]
    (g : R →+* P) (q : Ideal P) [q.IsPrime]
    (hlocq : q.primeCompl.IsLocalizationMap (algebraMap P S))
    (hfg : f = (algebraMap P S).comp g)
    (i₀ : A₀.Λ) (P₀ : Type uR) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra (A₀.RStage i₀) R] [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀)
    (hPalg : algebraMap R P = g)
    (e : P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P)
    (hσ_raw_comp : ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
      descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
        (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
          (descendedTailRawMap A₀ i₀ P₀ j k hjk))
    [IsDirectedOrder (Set.Ici i₀)]
    [DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h)]
    [DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h)]
    (bundle : JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :
    ∃ eTail :
        descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp ≃+* S,
      eTail.toRingHom =
        tail_target_colimit_to_ambient (S := S)
          (descendedTailRawStage A₀ i₀ P₀) (descendedTailRawMap A₀ i₀ P₀)
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e) hσ_raw_comp := by
  letI : IsDirectedOrder (Set.Ici i₀) := bundle.instTailDirected
  letI : DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h) := bundle.instDirectedSystemRaw
  letI : DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h) := bundle.instDirectedSystemTarget
  obtain ⟨inputs⟩ := joint_universe_target_colimit_inputs (f := f) (S := S) A₀ g hfg i₀ P₀
    hRalg hPalg e hσ_raw_comp bundle
  letI : Algebra (A₀.RStage i₀)
      (descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp) :=
    inputs.instAlgTargetLimit
  haveI : IsLocalization q.primeCompl S :=
    (isLocalization_iff_isLocalizationMap (M := q.primeCompl) (S := S)).mpr hlocq
  -- Proof comment: after shrinking the theorem boundary to `p0Alg`, `srcAlg`, and `ψ`, the
  -- mixed-universe tail-colimit equivalence theorem applies directly to the joint-universe tail.
  obtain ⟨eTail, hTail⟩ :=
    tailTargetColimitEquiv_mixed
      (S := S)
      (G := descendedTailRawStage A₀ i₀ P₀)
      (map := descendedTailRawMap A₀ i₀ P₀)
      (σ := descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (hσ := hσ_raw_comp)
      (q := q)
      (pComp := descendedTailPComp A₀ i₀ P₀ hRalg e)
      (hpComp := fun i ↦ rfl)
      inputs.psi
      inputs.hpsi
      inputs.hfactB
  exact ⟨eTail, hTail⟩

end
