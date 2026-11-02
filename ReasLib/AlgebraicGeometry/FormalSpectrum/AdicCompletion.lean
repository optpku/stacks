/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineScheme.FinitePresentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.WeaklyAdic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PresheafColimit
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Formal spectra of adic completions

Canonical evaluation maps compare the quotient-power completion with the formal
spectrum of the inverse-limit completion ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {A : Type u} [CommRing A]

/-- Evaluation at a quotient-power stage defines a weak ideal of definition
of the inverse-limit completion. -/
def evalWeakIdeal (I : Ideal A) (n : ℕ) :
    WeakIdealOfDefinition (AdicCompletion.WithLimitTopology I) :=
  WeakIdealOfDefinition.of (AdicCompletion.WithLimitTopology.evalKernel I n)
    (AdicCompletion.WithLimitTopology.evalKernel_isWeakIdealOfDefinition I n)

/-- The quotient-power spectrum maps to the quotient of the completion by the
kernel of evaluation, via the kernel lift of the canonical evaluation map. -/
def powerStageToLimitStage {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    powerStage structureHom I n ⟶
      stage (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I)
        (evalWeakIdeal I n) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (RingHom.kerLift (AdicCompletion.evalₐ I (n + 1)).toRingHom))) (by
      change Spec.map _ ≫ (Spec.map _ ≫ (Spec.map _ ≫ structureHom)) =
        Spec.map _ ≫ structureHom
      simp only [← Category.assoc, ← Spec.map_comp]
      rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem adicCompletion_eval_factor {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (show I ^ n • (⊤ : Ideal A) ≤ I ^ n by simp),
    ← AdicCompletion.factor_eval_eq_evalₐ I x (show I ^ m • (⊤ : Ideal A) ≤ I ^ m by simp)]
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
      (Ideal.Quotient.factor (show I ^ n • (⊤ : Ideal A) ≤ I ^ n by simp) (x.val n)) =
    Ideal.Quotient.factor (show I ^ m • (⊤ : Ideal A) ≤ I ^ m by simp) (x.val m)
  rw [← x.property h]
  generalize x.val n = a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation-induced stage maps form a cocone into the presheaf formal
spectrum of the inverse-limit completion. -/
def toSpfLimitCocone {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) :
    Cocone (powerThickenings structureHom I ⋙ yoneda) where
  pt := PresheafFormalSpectrum.spf (AdicCompletion.WithLimitTopology I)
    (completionStructureHom structureHom I)
  ι :=
    { app n :=
        yoneda.map (powerStageToLimitStage structureHom I n) ≫
          colimit.ι
            (thickenings (AdicCompletion.WithLimitTopology I)
              (completionStructureHom structureHom I) ⋙ yoneda)
            (evalWeakIdeal I n)
      naturality := by
        intro m n φ
        let f : evalWeakIdeal I m ⟶ evalWeakIdeal I n := homOfLE (by
          change RingHom.ker (AdicCompletion.evalₐ I (n + 1)).toRingHom ≤
            RingHom.ker (AdicCompletion.evalₐ I (m + 1)).toRingHom
          intro x hx
          change AdicCompletion.evalₐ I (n + 1) x = 0 at hx
          change AdicCompletion.evalₐ I (m + 1) x = 0
          rw [← adicCompletion_eval_factor I (Nat.succ_le_succ (leOfHom φ)) x, hx, map_zero])
        have hcomp : (powerThickenings structureHom I).map φ ≫
            powerStageToLimitStage structureHom I n =
            powerStageToLimitStage structureHom I m ≫
              (thickenings (AdicCompletion.WithLimitTopology I)
                (completionStructureHom structureHom I)).map f := by
          apply Over.OverMorphism.ext
          change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
          rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
          ext x
          change Ideal.Quotient.factor (Ideal.pow_le_pow_right
              (Nat.succ_le_succ (leOfHom φ)))
              ((AdicCompletion.evalₐ I (n + 1)).toRingHom.kerLift (Ideal.Quotient.mk _ x)) =
            (AdicCompletion.evalₐ I (m + 1)).toRingHom.kerLift (Ideal.Quotient.mk _ x)
          simp only [RingHom.kerLift_mk]
          exact adicCompletion_eval_factor I (Nat.succ_le_succ (leOfHom φ)) x
        change yoneda.map ((powerThickenings structureHom I).map φ) ≫ _ = _
        dsimp only [Functor.const]
        rw [Category.comp_id, ← Category.assoc, ← yoneda.map_comp, hcomp,
          yoneda.map_comp, Category.assoc]
        exact congrArg (fun g ↦ yoneda.map (powerStageToLimitStage structureHom I m) ≫ g)
          (colimit.w (thickenings (AdicCompletion.WithLimitTopology I)
            (completionStructureHom structureHom I) ⋙ yoneda) f) }

/-- The quotient-power presheaf completion maps canonically to the presheaf
formal spectrum of the inverse-limit completion ring. -/
def toSpfLimit {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I ⟶
      PresheafFormalSpectrum.spf (AdicCompletion.WithLimitTopology I)
        (completionStructureHom structureHom I) :=
  colimit.desc (powerThickenings structureHom I ⋙ yoneda)
    (toSpfLimitCocone structureHom I)

/-- On each quotient-power stage, the presheaf comparison is induced by the
kernel lift of evaluation followed by the weak-ideal colimit leg. -/
theorem toSpfLimit_ι {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n ≫ toSpfLimit structureHom I =
      yoneda.map (powerStageToLimitStage structureHom I n) ≫
        colimit.ι
          (thickenings (AdicCompletion.WithLimitTopology I)
            (completionStructureHom structureHom I) ⋙ yoneda)
          (evalWeakIdeal I n) :=
  colimit.ι_desc (toSpfLimitCocone structureHom I) n

/-- The evaluation comparison with the inverse-limit presheaf formal spectrum
is an isomorphism for every ideal. -/
instance isIso_toSpfLimit {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : Ideal A) : IsIso (toSpfLimit structureHom I) :=
  sorry

/-- The sheafified quotient-power completion maps canonically to the sheaf
formal spectrum of the inverse-limit completion. -/
def toSpfCompletion {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletionSheaf structureHom I ⟶
      spf (AdicCompletion.WithLimitTopology I) (completionStructureHom structureHom I) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
    (toSpfLimit structureHom I) ≫
      (spf_iso_sheafify_presheafColimit (AdicCompletion.WithLimitTopology I)
        (completionStructureHom structureHom I)).inv

set_option backward.isDefEq.respectTransparency false in
/-- On each sheafified quotient-power stage, the completion comparison is the
sheafified kernel-lift map followed by the canonical formal-spectrum leg. -/
theorem toSpfCompletion_ι {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfAdicCompletionι structureHom I n) ≫ toSpfCompletion structureHom I =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (yoneda.map (powerStageToLimitStage structureHom I n)) ≫
          spfι (AdicCompletion.WithLimitTopology I)
            (completionStructureHom structureHom I) (evalWeakIdeal I n) :=
  by
    let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type u)
    change F.map (spfAdicCompletionι structureHom I n) ≫
        (F.map (toSpfLimit structureHom I) ≫ _) = _
    rw [← Category.assoc, ← F.map_comp, toSpfLimit_ι, F.map_comp, Category.assoc]
    exact congrArg (fun f ↦ F.map (yoneda.map (powerStageToLimitStage structureHom I n)) ≫ f)
      (ι_preservesColimitIso_hom F
        (thickenings (AdicCompletion.WithLimitTopology I)
          (completionStructureHom structureHom I) ⋙ yoneda) (evalWeakIdeal I n))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from the sheafified quotient-power completion to
the sheaf formal spectrum of the inverse-limit completion is an isomorphism. -/
instance instIsIso_toSpfCompletion {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsIso (toSpfCompletion structureHom I) :=
  by
    unfold toSpfCompletion
    infer_instance

private theorem adicCompletion_colimit_target_iso {S : Scheme.{u}} {Λ : Type*}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] {D : Λ ⥤ Over S}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} (e : X ≅ Y)
    (h : IsDirectedAffineThickeningColimit D X) :
    IsDirectedAffineThickeningColimit D Y := by
  refine ⟨h.isAffine_obj, h.isThickening_map,
    (Presheaf.isSheaf_of_iso_iff e).mp h.isSheaf, ?_⟩
  obtain ⟨c, η, hc, hsurj, hinj⟩ := h.exists_colimit
  letI := hsurj
  letI := hinj
  exact ⟨c, η ≫ e.hom, hc, inferInstance, inferInstance⟩

private theorem adicCompletion_affine_target_iso {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} (e : X ≅ Y)
    (h : AffineFormalAlgebraicSpace.IsAffine X) :
    AffineFormalAlgebraicSpace.IsAffine Y := by
  obtain ⟨Λ, hΛ, hdir, D, hD⟩ := h.exists_colimit
  letI := hΛ
  letI := hdir
  refine ⟨⟨Λ, hΛ, hdir, D, adicCompletion_colimit_target_iso e hD⟩, ?_⟩
  obtain ⟨U, R, π, σ, hπ, hσ⟩ := h.exists_presentation
  letI := hπ
  letI := hσ
  let p := pullback.map π π (π ≫ e.hom) (π ≫ e.hom)
    (𝟙 _) (𝟙 _) e.hom (by simp) (by simp)
  haveI : IsIso p := by dsimp [p]; infer_instance
  exact ⟨U, R, π ≫ e.hom, σ ≫ p, inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified completion of an affine scheme along any ideal is weakly adic. -/
instance instIsWeaklyAdic_spfAdicCompletionSheaf {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsWeaklyAdic (spfAdicCompletionSheaf structureHom I).obj :=
  by
    let e := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).mapIso
      (asIso (toSpfCompletion structureHom I))
    have h : IsWeaklyAdic (spf (AdicCompletion.WithLimitTopology I)
      (completionStructureHom structureHom I)).obj := inferInstance
    refine { toIsAffine := adicCompletion_affine_target_iso e.symm h.toIsAffine
             exists_weaklyAdic := ?_ }
    obtain ⟨B, hB, hTop, hWeak, hAdm, σ, hcol⟩ := h.exists_weaklyAdic
    exact ⟨B, hB, hTop, hWeak, hAdm, σ, adicCompletion_colimit_target_iso e.symm hcol⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified completion along a finitely generated ideal is adic*. -/
theorem isAdicStar_of_fg {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    IsAdicStarAffine (spfAdicCompletionSheaf structureHom I).obj :=
  by
    letI := isIso_sheafifiedToCompletionAlong_of_fg structureHom I hI
    let e := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).mapIso
        (asIso (sheafifiedToCompletionAlong structureHom I)) ≪≫
      (isoSheafify (Scheme.fppfTopology.over S)
        (affineCompletionAlong_isSheaf structureHom (zeroLocusCloseds I))).symm
    have hcomp : IsCompact (zeroLocusCloseds I : Set (Spec (.of A)))ᶜ :=
      (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨I, hI, rfl⟩).1
    obtain ⟨B, hB, hTop, hAdic, J, hJ, hdef, σ, hcol⟩ :=
      (isAdicStar_completionAlong_of_isCompact_compl structureHom (zeroLocusCloseds I)
        hcomp).exists_adicStar
    exact ⟨⟨B, hB, hTop, hAdic, J, hJ, hdef, σ,
      adicCompletion_colimit_target_iso e.symm hcol⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified completion of a Noetherian affine scheme along an ideal is
Noetherian. -/
instance instIsNoetherianAffine_spfAdicCompletionSheaf {S : Scheme.{u}}
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    [AlgebraicGeometry.IsNoetherian (Spec (.of A))]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsNoetherianAffine (spfAdicCompletionSheaf structureHom I).obj :=
  by
    haveI : IsNoetherianRing A := (isNoetherian_Spec (R := .of A)).mp inferInstance
    have hI : I.FG := (isNoetherianRing_iff_ideal_fg A).mp inferInstance I
    letI := isIso_sheafifiedToCompletionAlong_of_fg structureHom I hI
    let e := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).mapIso
        (asIso (sheafifiedToCompletionAlong structureHom I)) ≪≫
      (isoSheafify (Scheme.fppfTopology.over S)
        (affineCompletionAlong_isSheaf structureHom (zeroLocusCloseds I))).symm
    obtain ⟨B, hB, hTop, hAdic, hN, J, hdef, σ, hcol⟩ :=
      (isNoetherian_completionAlong structureHom (zeroLocusCloseds I)).exists_adicNoetherian
    exact ⟨⟨B, hB, hTop, hAdic, hN, J, hdef, σ,
      adicCompletion_colimit_target_iso e.symm hcol⟩⟩

/-- Completion along an ideal is weakly adic; for a finitely generated ideal,
the extended ideal defines its adic topology, the canonical formal-spectrum
comparison is an isomorphism, and the completion is adic*. Completion of a
Noetherian affine scheme is Noetherian. -/
theorem completionAlongIdeal_types {S : Scheme.{u}} {A : Type u} [CommRing A]
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsWeaklyAdic (spfAdicCompletionSheaf structureHom I).obj ∧
      (I.FG →
        IsAdic (I.map (algebraMap A (AdicCompletion.WithLimitTopology I))) ∧
          IsIso (toSpfCompletion structureHom I) ∧
            IsAdicStarAffine (spfAdicCompletionSheaf structureHom I).obj) ∧
      (AlgebraicGeometry.IsNoetherian (Spec (.of A)) →
        IsNoetherianAffine (spfAdicCompletionSheaf structureHom I).obj) :=
  by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro hI
      exact ⟨AdicCompletion.WithLimitTopology.isAdic_of_fg I hI, inferInstance,
        isAdicStar_of_fg structureHom I hI⟩
    · intro hA
      letI := hA
      infer_instance

end AlgebraicGeometry.AffineFormalAlgebraicSpace
