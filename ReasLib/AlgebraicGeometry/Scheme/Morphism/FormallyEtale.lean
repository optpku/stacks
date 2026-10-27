/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Locus

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism of schemes is formally étale when its maps on affine coordinate rings are
formally étale. -/
class FormallyEtale (f : X ⟶ S) : Prop where
  /-- The induced ring map on compatible affine opens is formally étale. -/
  formallyEtale_appLE (f) :
    ∀ {U : S.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyEtale

namespace Scheme.Hom

/-- Formal étaleness supplies formal étaleness of the induced map on affine coordinate
rings. -/
alias formallyEtale_appLE := FormallyEtale.formallyEtale_appLE

end Scheme.Hom

namespace FormallyEtale

private lemma ringHom_stableUnderComposition :
    RingHom.StableUnderComposition RingHom.FormallyEtale :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg

private lemma ringHom_holdsForLocalizationAway :
    RingHom.HoldsForLocalizationAway RingHom.FormallyEtale :=
  fun _ _ _ _ _ r _ ↦ RingHom.formallyEtale_algebraMap.mpr
    (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r))

private lemma ringHom_respectsIso : RingHom.RespectsIso RingHom.FormallyEtale :=
  ringHom_stableUnderComposition.respectsIso fun e ↦
    ringHom_holdsForLocalizationAway.of_bijective _ _ e.bijective

private lemma ringHom_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.FormallyEtale := by
  refine .mk ringHom_respectsIso ?_
  introv H
  rw [RingHom.formallyEtale_algebraMap] at H ⊢
  infer_instance

private lemma ringHom_ofLocalizationSpanTarget :
    RingHom.OfLocalizationSpanTarget RingHom.FormallyEtale := by
  intro R S _ _ f s hs hf
  algebraize [f]
  change Algebra.FormallyEtale R S
  rw [← Algebra.etaleLocus_eq_univ_iff, ← Set.univ_subset_iff,
    ← TopologicalSpace.Opens.coe_top, ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_etaleLocus_iff, ← RingHom.formallyEtale_algebraMap]
  exact fun r hr ↦ hf ⟨r, hr⟩

/-- Scheme-level formal étaleness is associated with ring-level formal étaleness. -/
instance instHasRingHomProperty :
    HasRingHomProperty (@FormallyEtale.{u}) RingHom.FormallyEtale where
  isLocal_ringHomProperty := {
    localizationAwayPreserves := ringHom_isStableUnderBaseChange.localizationPreserves.away
    ofLocalizationSpanTarget := ringHom_ofLocalizationSpanTarget
    ofLocalizationSpan := ringHom_ofLocalizationSpanTarget.ofLocalizationSpan
      (ringHom_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        ringHom_holdsForLocalizationAway).1
    StableUnderCompositionWithLocalizationAwayTarget :=
      (ringHom_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        ringHom_holdsForLocalizationAway).2 }
  eq_affineLocally' := by
    ext X S f
    rw [affineLocally_iff_forall_isAffineOpen]
    exact ⟨fun h ↦ h.formallyEtale_appLE, fun h ↦ ⟨h⟩⟩

/-- A morphism between affine schemes is formally étale if and only if its induced map on
global sections is formally étale. -/
theorem iff_of_isAffine [IsAffine X] [IsAffine S] :
    FormallyEtale f ↔ f.appTop.hom.FormallyEtale :=
  HasRingHomProperty.iff_of_isAffine

/-- Formally étale scheme morphisms are stable under composition. -/
instance instIsStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@FormallyEtale.{u}) :=
  HasRingHomProperty.stableUnderComposition ringHom_stableUnderComposition

/-- Formal étaleness contains identities and is stable under composition. -/
instance instIsMultiplicative :
    MorphismProperty.IsMultiplicative (@FormallyEtale.{u}) :=
  HasRingHomProperty.isMultiplicative ringHom_stableUnderComposition
    ringHom_holdsForLocalizationAway.containsIdentities

/-- Formally étale scheme morphisms are stable under base change. -/
instance instIsStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@FormallyEtale.{u}) :=
  HasRingHomProperty.isStableUnderBaseChange ringHom_isStableUnderBaseChange

/-- Every formally étale scheme morphism is formally unramified. -/
instance toFormallyUnramified [FormallyEtale f] : FormallyUnramified f where
  formallyUnramified_appLE {_} hU {_} hV e := by
    have := f.formallyEtale_appLE hU hV e
    algebraize [(f.appLE _ _ e).hom]
    exact inferInstanceAs (Algebra.FormallyUnramified _ _)

open CategoryTheory.Limits TopologicalSpace

private lemma ker_restrict_sq {T T' : Scheme.{u}} (i : T ⟶ T') [IsClosedImmersion i]
    (hi : i.ker ^ 2 = ⊥) (W : T'.Opens) : (i ∣_ W).ker ^ 2 = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext V
  change (i ∣_ W).ker.ideal V ^ 2 = ⊥
  rw [Scheme.ker_morphismRestrict_ideal]
  exact congrArg (fun J : T'.IdealSheafData ↦
    J.ideal ⟨W.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩) hi

private lemma surj_of_ker_sq {T T' : Scheme.{u}} (i : T ⟶ T') [IsClosedImmersion i]
    (hi : i.ker ^ 2 = ⊥) : Surjective i := by
  have : IsDominant i := by
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow 2 (by decide), hi]
    simp
  exact surjective_of_isDominant_of_isClosed_range _ i.isClosedEmbedding.isClosed_range

private lemma exists_lift_on_open {X S T T' : Scheme.{u}} (f : X ⟶ S) [FormallyEtale f]
    (i : T ⟶ T') [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)
    (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (W : T'.Opens) (hW : IsAffineOpen W)
    (eb : W ≤ h ⁻¹ᵁ U) (ea : i ⁻¹ᵁ W ≤ g ⁻¹ᵁ V) :
    ∃ l : W.toScheme ⟶ X,
      (i ∣_ W) ≫ l = (i ⁻¹ᵁ W).ι ≫ g ∧ l ≫ f = W.ι ≫ h := by
  have := f.formallyEtale_appLE hU hV e
  algebraize [(f.appLE U V e).hom, (h.appLE U W eb).hom, (i.app W).hom,
    (h.appLE U W eb ≫ i.app W).hom]
  have hcomm : f.appLE U V e ≫ g.appLE V (i ⁻¹ᵁ W) ea =
      h.appLE U W eb ≫ i.app W := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, sq.w]
  let g₀ : Γ(X, V) →ₐ[Γ(S, U)] Γ(T, i ⁻¹ᵁ W) :=
    ⟨(g.appLE V (i ⁻¹ᵁ W) ea).hom,
      fun r ↦ congrArg (fun k : Γ(S, U) ⟶ Γ(T, i ⁻¹ᵁ W) ↦ k r) hcomm⟩
  let i₀ : Γ(T', W) →ₐ[Γ(S, U)] Γ(T, i ⁻¹ᵁ W) :=
    ⟨(i.app W).hom, fun r ↦ rfl⟩
  have hsurj : Function.Surjective i₀ := i.app_surjective W hW
  have hnil : IsNilpotent (RingHom.ker i₀.toRingHom) :=
    ⟨2, by simpa [i₀] using congrArg (fun J : T'.IdealSheafData ↦ J.ideal ⟨W, hW⟩) hi⟩
  let ψ := Algebra.FormallySmooth.liftOfSurjective g₀ i₀ hsurj hnil
  have hleft : CommRingCat.ofHom ψ.toRingHom ≫ i.app W = g.appLE V (i ⁻¹ᵁ W) ea :=
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom
      (Algebra.FormallySmooth.comp_liftOfSurjective g₀ i₀ hsurj hnil))
  have hright : f.appLE U V e ≫ CommRingCat.ofHom ψ.toRingHom = h.appLE U W eb :=
    CommRingCat.hom_ext ψ.comp_algebraMap
  refine ⟨W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← Scheme.Opens.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, hleft,
      Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hV.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  · rw [Category.assoc, Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e,
      ← Spec.map_comp_assoc, hright, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
      hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

private lemma specMap_ker_sq {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    (Spec.map φ).ker ^ 2 = ⊥ := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  apply Scheme.IdealSheafData.ext_of_isAffine
  change (Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top _⟩ ^ 2 = ⊥
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥
  have hk : RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv,
      RingHom.comap_ker, RingEquiv.toRingHom_eq_coe,
      Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp,
      Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, ← RingHom.comap_ker]
  rw [hk]
  apply le_antisymm _ bot_le
  calc
    _ ≤ (RingHom.ker φ.hom ^ 2).comap (Scheme.ΓSpecIso R).hom.hom :=
      Ideal.le_comap_pow _ _
    _ = ⊥ := by
      rw [hker]
      exact (RingHom.injective_iff_ker_eq_bot _).mp (ConcreteCategory.bijective_of_isIso _).1

/-- A formally étale scheme morphism has a unique lift from every affine first-order
thickening. -/
theorem existsUnique_lift [FormallyEtale f] {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (i : T ⟶ T') [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (g : T ⟶ X)
    (h : T' ⟶ S) (sq : CommSq g i f h) : Nonempty (Unique sq.LiftStruct) := by
  classical
  have : Surjective i := surj_of_ker_sq i hi
  have hloc : ∀ x : T', ∃ (W : T'.Opens) (_ : x ∈ W) (l : W.toScheme ⟶ X),
      (i ∣_ W) ≫ l = (i ⁻¹ᵁ W).ι ≫ g ∧ l ≫ f = W.ι ≫ h := by
    intro x
    obtain ⟨t, rfl⟩ := i.surjective x
    obtain ⟨_, ⟨U, hU, rfl⟩, htU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g t))) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, htV, e⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open htU (f ⁻¹ᵁ U).isOpen
    obtain ⟨A, hA, hAi⟩ :=
      i.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp (g ⁻¹ᵁ V).isOpen
    have htA : i t ∈ A := by
      change t ∈ i ⁻¹' A
      rw [hAi]
      exact htV
    have htU' : h (i t) ∈ U := by
      change (i ≫ h) t ∈ (U : Set S)
      rw [← sq.w]
      exact htU
    obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWA⟩ :=
      T'.isBasis_affineOpens.exists_subset_of_mem_open
        (show i t ∈ (⟨A, hA⟩ : T'.Opens) ⊓ h ⁻¹ᵁ U from ⟨htA, htU'⟩)
        ((⟨A, hA⟩ : T'.Opens) ⊓ h ⁻¹ᵁ U).isOpen
    have ea : i ⁻¹ᵁ W ≤ g ⁻¹ᵁ V := by
      intro y hy
      change y ∈ (g ⁻¹ᵁ V : Set T)
      rw [← hAi]
      exact (hWA hy).1
    obtain ⟨l, hl, hr⟩ := exists_lift_on_open f i hi g h sq hU hV e W hW
      (hWA.trans inf_le_right) ea
    exact ⟨W, htW, l, hl, hr⟩
  choose W hx l hl hr using hloc
  have hcompat : ∀ j k,
      T'.homOfLE (inf_le_left : W j ⊓ W k ≤ W j) ≫ l j =
        T'.homOfLE (inf_le_right : W j ⊓ W k ≤ W k) ≫ l k := by
    intro j k
    have h₁ : i ∣_ (W j ⊓ W k) ≫ T'.homOfLE inf_le_left =
        T.homOfLE (show i ⁻¹ᵁ (W j ⊓ W k) ≤ i ⁻¹ᵁ W j from fun _ hx ↦ hx.1) ≫
          i ∣_ W j := by
      simp [← cancel_mono (W j).ι]
    have h₂ : i ∣_ (W j ⊓ W k) ≫ T'.homOfLE inf_le_right =
        T.homOfLE (show i ⁻¹ᵁ (W j ⊓ W k) ≤ i ⁻¹ᵁ W k from fun _ hx ↦ hx.2) ≫
          i ∣_ W k := by
      simp [← cancel_mono (W k).ι]
    apply FormallyUnramified.hom_ext (i ∣_ (W j ⊓ W k))
      ⟨2, ker_restrict_sq i hi _⟩ f
    · calc
        _ = (i ⁻¹ᵁ (W j ⊓ W k)).ι ≫ g := by
          rw [← Category.assoc, h₁, Category.assoc, hl j, Scheme.homOfLE_ι_assoc]
        _ = _ := by
          rw [← Category.assoc, h₂, Category.assoc, hl k, Scheme.homOfLE_ι_assoc]
    · simp only [Category.assoc, hr, Scheme.homOfLE_ι_assoc]
  have hc : IsOpenCover W := .mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
  let 𝒰 := T'.openCoverOfIsOpenCover W hc
  have hglue : ∀ j k, pullback.fst (𝒰.f j) (𝒰.f k) ≫ l j =
      pullback.snd _ _ ≫ l k := by
    change ∀ j k : T', pullback.fst (W j).ι (W k).ι ≫ l j =
      pullback.snd _ _ ≫ l k
    intro j k
    apply (cancel_epi (isPullback_opens_inf (W j) (W k)).isoPullback.hom).mp
    simpa only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc] using hcompat j k
  let lift := 𝒰.glueMorphisms l hglue
  have hleft : i ≫ lift = g := by
    let 𝒱 := T.openCoverOfIsOpenCover (fun j ↦ i ⁻¹ᵁ W j)
      (.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨i x, hx (i x)⟩))
    apply 𝒱.hom_ext
    change ∀ j : T', (i ⁻¹ᵁ W j).ι ≫ i ≫ lift = (i ⁻¹ᵁ W j).ι ≫ g
    intro j
    have hfac : (W j).ι ≫ lift = l j := 𝒰.ι_glueMorphisms l hglue j
    rw [← morphismRestrict_ι_assoc, hfac, hl j]
  have hright : lift ≫ f = h := by
    apply 𝒰.hom_ext
    change ∀ j : T', (W j).ι ≫ lift ≫ f = (W j).ι ≫ h
    intro j
    have hfac : (W j).ι ≫ lift = l j := 𝒰.ι_glueMorphisms l hglue j
    rw [← Category.assoc, hfac, hr j]
  refine ⟨{ default := ⟨lift, hleft, hright⟩, uniq := ?_ }⟩
  intro m
  apply CommSq.LiftStruct.ext
  exact FormallyUnramified.hom_ext i ⟨2, hi⟩ f
    (m.fac_left.trans hleft.symm) (m.fac_right.trans hright.symm)

/-- The unique lifting property for affine first-order thickenings implies formal étaleness. -/
theorem of_existsUnique_lift
    (h_lift : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
      [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (g : T ⟶ X) (h : T' ⟶ S)
      (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct)) : FormallyEtale f := by
  have : FormallyUnramified f := FormallyUnramified.of_hom_ext f (by
    intro R S φ hφ hker g₁ g₂ hleft hright
    have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
    let sq : CommSq (Spec.map φ ≫ g₁) (Spec.map φ) f (g₁ ≫ f) := ⟨by simp⟩
    obtain ⟨h⟩ := h_lift (Spec.map φ) (specMap_ker_sq φ hφ hker) _ _ sq
    let l₁ : sq.LiftStruct := ⟨g₁, rfl, rfl⟩
    let l₂ : sq.LiftStruct := ⟨g₂, hleft.symm, hright.symm⟩
    exact congrArg CommSq.LiftStruct.l ((h.uniq l₁).trans (h.uniq l₂).symm))
  refine ⟨fun {U} hU {V} hV e ↦ ?_⟩
  have := f.formallyUnramified_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  have : Algebra.FormallySmooth Γ(S, U) Γ(X, V) := by
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI g
    let φ : CommRingCat.of B ⟶ CommRingCat.of (B ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mk I)
    have : IsClosedImmersion (Spec.map φ) :=
      IsClosedImmersion.spec_of_surjective φ Ideal.Quotient.mk_surjective
    have hi : (Spec.map φ).ker ^ 2 = ⊥ :=
      specMap_ker_sq φ Ideal.Quotient.mk_surjective (by simpa [φ] using hI)
    have : Surjective (Spec.map φ) := surj_of_ker_sq (Spec.map φ) hi
    let a : Spec (.of (B ⧸ I)) ⟶ X :=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec
    let b : Spec (.of B) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) B)) ≫ hU.fromSpec
    have hg : f.appLE U V e ≫ CommRingCat.ofHom g.toRingHom =
        CommRingCat.ofHom (algebraMap Γ(S, U) (B ⧸ I)) :=
      CommRingCat.hom_ext g.comp_algebraMap
    let sq : CommSq a (Spec.map φ) f b := ⟨by
      simp only [a, b, Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e,
        ← Spec.map_comp_assoc, hg]
      rfl⟩
    obtain ⟨lift⟩ := h_lift (Spec.map φ) hi a b sq
    have hrange : Set.range lift.default.l ⊆ Set.range hV.fromSpec := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := (Spec.map φ).surjective x
      exact ⟨Spec.map (CommRingCat.ofHom g.toRingHom) y,
        (congrArg (fun k : Spec (.of (B ⧸ I)) ⟶ X ↦ k y) lift.default.fac_left).symm⟩
    let l := IsOpenImmersion.lift hV.fromSpec lift.default.l hrange
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective l
    have hleft : Spec.map φ ≫ Spec.map ψ = Spec.map (CommRingCat.ofHom g.toRingHom) := by
      rw [← cancel_mono hV.fromSpec]
      simpa [hψ, l, a] using lift.default.fac_left
    have hright : Spec.map ψ ≫ Spec.map (f.appLE U V e) =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) B)) := by
      rw [← cancel_mono hU.fromSpec]
      simpa [hψ, l, b, hU.SpecMap_appLE_fromSpec f hV e] using lift.default.fac_right
    have hψcomm' : f.appLE U V e ≫ ψ =
        CommRingCat.ofHom (algebraMap Γ(S, U) B) := by
      apply Spec.map_injective
      simpa only [Spec.map_comp] using hright
    have hψcomm : ψ.hom.comp (f.appLE U V e).hom = algebraMap Γ(S, U) B :=
      congrArg CommRingCat.Hom.hom hψcomm'
    let ψₐ : Γ(X, V) →ₐ[Γ(S, U)] B := ⟨ψ.hom, RingHom.congr_fun hψcomm⟩
    refine ⟨ψₐ, ?_⟩
    have hcomp : ψ ≫ φ = CommRingCat.ofHom g.toRingHom := by
      apply Spec.map_injective
      simpa only [Spec.map_comp] using hleft
    apply AlgHom.ext
    intro x
    exact congrArg (fun k : Γ(X, V) ⟶ .of (B ⧸ I) ↦ k x) hcomp
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- Formal étaleness is equivalent to unique lifting from affine first-order thickenings. -/
theorem iff_existsUnique_lift :
    FormallyEtale f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (g : T ⟶ X) (h : T' ⟶ S)
        (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct) := by
  constructor
  · intro hf
    letI : FormallyEtale f := hf
    intro T T' _ _ i _ hi g h sq
    exact existsUnique_lift f i hi g h sq
  · exact of_existsUnique_lift f

end FormallyEtale

end AlgebraicGeometry
