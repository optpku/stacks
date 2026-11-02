/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact Short Complexes of Finite Filtered Objects

This file provides the reusable exactness-detection API for a short complex of filtered objects.
Associated-graded exactness first descends degreewise, then detects exactness on stages and
quotients for finite filtrations.  Two independent bridge theorems expose the strictness
criteria used by the combined result.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.ShortComplex

open FilteredObject FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (FilteredObject C)}

namespace Filtered

private theorem cokernel_extension_shortExact {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hfg : f ≫ g = h) [Mono g] :
    (ShortComplex.mk
      (cokernel.map f h (𝟙 _) g (by rw [Category.id_comp]; exact hfg))
      (cokernel.map h g f (𝟙 _) (by rw [Category.comp_id]; exact hfg.symm))
      (by
        apply (cancel_epi (cokernel.π f)).1
        simp only [cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc, Category.id_comp,
          cokernel.condition, comp_zero])).ShortExact := by
  subst h
  let φ : ShortComplex.mk f (cokernel.π f) (cokernel.condition f) ⟶
      ShortComplex.mk (f ≫ g) (cokernel.π (f ≫ g)) (cokernel.condition (f ≫ g)) :=
    homMk (𝟙 _) g (cokernel.map f (f ≫ g) (𝟙 _) g (by rw [Category.id_comp]))
      (by rw [Category.id_comp]) (by simp only [cokernel.π_desc])
  haveI : Mono (cokernel.map f (f ≫ g) (𝟙 _) g (by rw [Category.id_comp])) :=
    mono_of_epi_of_epi_of_mono φ (exact_cokernel _)
      (by change Epi (cokernel.π f); infer_instance)
      (by change Epi (𝟙 A); infer_instance) (by change Mono g; infer_instance)
  haveI : Epi (cokernel.map (f ≫ g) g f (𝟙 _) (by rw [Category.comp_id])) :=
    epi_of_epi_fac (show cokernel.π (f ≫ g) ≫
      cokernel.map (f ≫ g) g f (𝟙 _) (by rw [Category.comp_id]) = cokernel.π g by
        simp only [cokernel.π_desc, Category.id_comp])
  exact ⟨(kernelCokernelCompSequence_exact f g).exact 3⟩

private theorem exact_of_extension {L M R : ShortComplex C}
    (i : L ⟶ M) (q : M ⟶ R) (w : i.τ₂ ≫ q.τ₂ = 0)
    [Mono i.τ₂] [Mono i.τ₃] [Epi q.τ₁]
    (hcol : (ShortComplex.mk i.τ₂ q.τ₂ w).Exact)
    (hL : L.Exact) (hR : R.Exact) : M.Exact := by
  rw [exact_iff_exact_up_to_refinements]
  intro A x hx
  have hxq : (x ≫ q.τ₂) ≫ R.g = 0 := by
    rw [Category.assoc, q.comm₂₃, ← Category.assoc, hx, zero_comp]
  obtain ⟨A₁, e₁, he₁, y, hy⟩ := hR.exact_up_to_refinements _ hxq
  obtain ⟨A₂, e₂, he₂, z, hz⟩ := surjective_up_to_refinements_of_epi q.τ₁ y
  let d := e₂ ≫ e₁ ≫ x - z ≫ M.f
  have hd : d ≫ q.τ₂ = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, sub_eq_zero]
    calc
      (e₂ ≫ e₁ ≫ x) ≫ q.τ₂ = e₂ ≫ (e₁ ≫ (x ≫ q.τ₂)) := by
        simp only [Category.assoc]
      _ = e₂ ≫ (y ≫ R.f) := by rw [hy]
      _ = (z ≫ q.τ₁) ≫ R.f := by rw [← Category.assoc, hz]
      _ = (z ≫ M.f) ≫ q.τ₂ := by rw [Category.assoc, q.comm₁₂, Category.assoc]
  let t := hcol.lift d hd
  have ht : t ≫ i.τ₂ = d := hcol.lift_f d hd
  have htg : t ≫ L.g = 0 := by
    apply (cancel_mono i.τ₃).1
    rw [zero_comp, Category.assoc, ← i.comm₂₃, ← Category.assoc, ht]
    simp only [d, Preadditive.sub_comp, Category.assoc, hx, M.zero,
      comp_zero, sub_self]
  obtain ⟨A₃, e₃, he₃, u, hu⟩ := hL.exact_up_to_refinements t htg
  refine ⟨A₃, e₃ ≫ e₂ ≫ e₁, inferInstance, e₃ ≫ z + u ≫ i.τ₁, ?_⟩
  calc
    (e₃ ≫ e₂ ≫ e₁) ≫ x = e₃ ≫ (d + z ≫ M.f) := by
      simp only [d, sub_add_cancel, Category.assoc]
    _ = e₃ ≫ d + (e₃ ≫ z) ≫ M.f := by
      rw [Preadditive.comp_add, Category.assoc]
    _ = (u ≫ i.τ₁) ≫ M.f + (e₃ ≫ z) ≫ M.f := by
      rw [← ht, ← Category.assoc, hu, Category.assoc, ← i.comm₁₂, ← Category.assoc]
    _ = (e₃ ≫ z + u ≫ i.τ₁) ≫ M.f := by
      rw [Preadditive.add_comp, add_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem strict_f_of_stages
    (hstage : ∀ p : ℤ, (S.map (Stage.functor p)).Exact) : Strict S.f := by
  have hfg : S.f.hom ≫ S.g.hom = 0 :=
    congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom) S.zero
  intro p
  apply le_antisymm
  · exact le_inf (imageSubobject_comp_le _ _)
      (imageSubobject_le _ (S.f.stageMap p) (S.f.stageMap_arrow p))
  · let I := imageSubobject S.f.hom ⊓ S.X₂.filtration.stage p
    let k : (I : C) ⟶ S.X₂.stage p := Subobject.ofLE _ _ inf_le_right
    have hk : k ≫ S.g.stageMap p = 0 := by
      apply (cancel_mono (S.X₃.filtration.stage p).arrow).1
      rw [zero_comp, Category.assoc, stageMap_arrow, ← Category.assoc,
        Subobject.ofLE_arrow]
      rw [← Subobject.ofLE_arrow (show I ≤ imageSubobject S.f.hom from inf_le_left),
        Category.assoc, imageSubobject_arrow_comp_eq_zero hfg, comp_zero]
    obtain ⟨W, e, he, a, ha⟩ := (hstage p).exact_up_to_refinements k hk
    change e ≫ k = a ≫ S.f.stageMap p at ha
    have hfac : e ≫ I.arrow = a ≫ ((S.X₁.filtration.stage p).arrow ≫ S.f.hom) := by
      rw [← S.f.stageMap_arrow p, ← Category.assoc, ← ha, Category.assoc,
        Subobject.ofLE_arrow]
    calc
      I = imageSubobject I.arrow := by rw [imageSubobject_mono, Subobject.mk_arrow]
      _ = imageSubobject (e ≫ I.arrow) :=
        (imageSubobject_comp_eq_of_epi_left e I.arrow).symm
      _ ≤ imageSubobject ((S.X₁.filtration.stage p).arrow ≫ S.f.hom) := by
        rw [hfac]
        exact imageSubobject_comp_le _ _

set_option backward.isDefEq.respectTransparency false in
private theorem strict_g_of_quotients
    (hquot : ∀ p : ℤ, (S.map (quotientFunctor p)).Exact) : Strict S.g := by
  have hfg : S.f.hom ≫ S.g.hom = 0 :=
    congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom) S.zero
  intro p
  apply le_antisymm
  · exact le_inf (imageSubobject_comp_le _ _)
      (imageSubobject_le _ (S.g.stageMap p) (S.g.stageMap_arrow p))
  · let I := imageSubobject S.g.hom ⊓ S.X₃.filtration.stage p
    obtain ⟨W, e, he, x, hx⟩ := surjective_up_to_refinements_of_epi
      (factorThruImageSubobject S.g.hom)
      (Subobject.ofLE I (imageSubobject S.g.hom) inf_le_left)
    have hxg : x ≫ S.g.hom = e ≫ I.arrow := by
      rw [← imageSubobject_arrow_comp S.g.hom, ← Category.assoc, ← hx,
        Category.assoc, Subobject.ofLE_arrow]
    have hi : I.arrow ≫ cokernel.π (S.X₃.filtration.stage p).arrow = 0 := by
      rw [← Subobject.ofLE_arrow (show I ≤ S.X₃.filtration.stage p from inf_le_right),
        Category.assoc, cokernel.condition, comp_zero]
    have hxq : (x ≫ cokernel.π (S.X₂.filtration.stage p).arrow) ≫
        S.g.quotientMap p = 0 := by
      rw [Category.assoc, quotientMap_comm, ← Category.assoc, hxg,
        Category.assoc, hi, comp_zero]
    obtain ⟨W', e', he', a, ha⟩ := (hquot p).exact_up_to_refinements _ hxq
    change e' ≫ (x ≫ cokernel.π (S.X₂.filtration.stage p).arrow) =
      a ≫ S.f.quotientMap p at ha
    obtain ⟨W'', e'', he'', b, hb⟩ := surjective_up_to_refinements_of_epi
      (cokernel.π (S.X₁.filtration.stage p).arrow) a
    let d := e'' ≫ e' ≫ x - b ≫ S.f.hom
    have hd : d ≫ cokernel.π (S.X₂.filtration.stage p).arrow = 0 := by
      dsimp only [d]
      rw [Preadditive.sub_comp, sub_eq_zero]
      calc
        (e'' ≫ e' ≫ x) ≫ cokernel.π (S.X₂.filtration.stage p).arrow =
            e'' ≫ (e' ≫ (x ≫ cokernel.π (S.X₂.filtration.stage p).arrow)) := by
          simp only [Category.assoc]
        _ = e'' ≫ (a ≫ S.f.quotientMap p) := by rw [ha]
        _ = (b ≫ cokernel.π (S.X₁.filtration.stage p).arrow) ≫ S.f.quotientMap p := by
          rw [← Category.assoc, hb]
        _ = (b ≫ S.f.hom) ≫ cokernel.π (S.X₂.filtration.stage p).arrow := by
          rw [Category.assoc, quotientMap_comm, ← Category.assoc]
    let t := (exact_cokernel (S.X₂.filtration.stage p).arrow).lift d hd
    have ht : t ≫ (S.X₂.filtration.stage p).arrow = d :=
      (exact_cokernel (S.X₂.filtration.stage p).arrow).lift_f d hd
    have hfac : (e'' ≫ e' ≫ e) ≫ I.arrow =
        t ≫ ((S.X₂.filtration.stage p).arrow ≫ S.g.hom) := by
      rw [← Category.assoc t, ht]
      simp only [d, Preadditive.sub_comp, Category.assoc, hfg, comp_zero, sub_zero, hxg]
    calc
      I = imageSubobject I.arrow := by rw [imageSubobject_mono, Subobject.mk_arrow]
      _ = imageSubobject ((e'' ≫ e' ≫ e) ≫ I.arrow) :=
        (imageSubobject_comp_eq_of_epi_left _ I.arrow).symm
      _ ≤ imageSubobject ((S.X₂.filtration.stage p).arrow ≫ S.g.hom) := by
        rw [hfac]
        exact imageSubobject_comp_le _ _

private theorem exact_underlying_of_stages
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite)
    (hstage : ∀ p : ℤ, (S.map (Stage.functor p)).Exact) :
    (S.map FilteredObject.forget).Exact := by
  obtain ⟨n₁, m₁, hn₁, hm₁⟩ := hX₁fin
  obtain ⟨n₂, m₂, hn₂, hm₂⟩ := hX₂fin
  let p := min n₁ n₂
  have ht₁ : S.X₁.filtration.stage p = ⊤ := by
    apply top_unique
    rw [← hn₁]
    exact S.X₁.filtration.antitone (min_le_left _ _)
  have ht₂ : S.X₂.filtration.stage p = ⊤ := by
    apply top_unique
    rw [← hn₂]
    exact S.X₂.filtration.antitone (min_le_right _ _)
  let φ := S.mapNatTrans (Stage.toForget p)
  haveI : IsIso φ.τ₁ := (Subobject.isIso_arrow_iff_eq_top _).2 ht₁
  haveI : IsIso φ.τ₂ := (Subobject.isIso_arrow_iff_eq_top _).2 ht₂
  haveI : Mono φ.τ₃ := by
    change Mono (S.X₃.filtration.stage p).arrow
    infer_instance
  exact (exact_iff_of_epi_of_isIso_of_mono φ).1 (hstage p)

namespace AssociatedGraded

/-- Exactness of an associated-graded short complex can be evaluated in every degree. -/
@[stacks 05QH]
theorem exact_piece
    (hgr : (S.map associatedGradedFunctor).Exact) (p : ℤ) :
    (S.map (associatedGradedFunctor ⋙ GradedObject.eval p)).Exact := by
  simpa only [ShortComplex.map_comp] using hgr.map (GradedObject.eval p)

set_option backward.isDefEq.respectTransparency false in
/-- For finite filtrations, associated-graded exactness implies exactness on every filtration
stage. -/
@[stacks 05QH]
theorem exact_stage
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) (p : ℤ) :
    (S.map (Stage.functor p)).Exact := by
  have step (p : ℤ) (hs : (S.map (Stage.functor (p + 1))).Exact) :
      (S.map (Stage.functor p)).Exact := by
    let i : S.map (Stage.functor (p + 1)) ⟶ S.map (Stage.functor p) :=
      homMk (S.X₁.filtration.succInclusion p) (S.X₂.filtration.succInclusion p)
        (S.X₃.filtration.succInclusion p)
        (succInclusion_naturality S.f p) (succInclusion_naturality S.g p)
    let q : S.map (Stage.functor p) ⟶
        S.map (associatedGradedFunctor ⋙ GradedObject.eval p) :=
      homMk (cokernel.π (S.X₁.filtration.succInclusion p))
        (cokernel.π (S.X₂.filtration.succInclusion p))
        (cokernel.π (S.X₃.filtration.succInclusion p))
        (by
          change cokernel.π (S.X₁.filtration.succInclusion p) ≫ S.f.gradedPieceMap p =
            S.f.stageMap p ≫ cokernel.π (S.X₂.filtration.succInclusion p)
          simp only [Hom.gradedPieceMap, cokernel.π_desc])
        (by
          change cokernel.π (S.X₂.filtration.succInclusion p) ≫ S.g.gradedPieceMap p =
            S.g.stageMap p ≫ cokernel.π (S.X₃.filtration.succInclusion p)
          simp only [Hom.gradedPieceMap, cokernel.π_desc])
    haveI : Mono i.τ₂ := by change Mono (S.X₂.filtration.succInclusion p); infer_instance
    haveI : Mono i.τ₃ := by change Mono (S.X₃.filtration.succInclusion p); infer_instance
    haveI : Epi q.τ₁ := by
      change Epi (cokernel.π (S.X₁.filtration.succInclusion p))
      infer_instance
    exact exact_of_extension i q (cokernel.condition _)
      (exact_cokernel _) hs (exact_piece hgr p)
  obtain ⟨n, m, hn, hm⟩ := hX₂fin
  have base (k : ℤ) (hmk : m ≤ k) : (S.map (Stage.functor k)).Exact := by
    apply exact_of_isZero_X₂
    change IsZero ((S.X₂.filtration.stage k : Subobject S.X₂.obj) : C)
    have hk : S.X₂.filtration.stage k = ⊥ :=
      bot_unique ((S.X₂.filtration.antitone hmk).trans_eq hm)
    rw [hk]
    exact IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero
  refine Int.inductionOn' p m (base m le_rfl) (fun k hmk _ ↦ ?_) (fun k _ ih ↦ ?_)
  · exact base (k + 1) (Int.le_add_one hmk)
  · apply step (k - 1)
    simpa only [sub_add_cancel] using ih

set_option backward.isDefEq.respectTransparency false in
/-- For finite filtrations, associated-graded exactness implies exactness after quotienting by
every filtration stage. -/
@[stacks 05QH]
theorem exact_quotient
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) (p : ℤ) :
    (S.map (quotientFunctor p)).Exact := by
  have step (p : ℤ) (hs : (S.map (quotientFunctor p)).Exact) :
      (S.map (quotientFunctor (p + 1))).Exact := by
    let i (X : FilteredObject C) : X.gradedPiece p ⟶ X.quotient (p + 1) :=
      cokernel.map (X.filtration.succInclusion p) (X.filtration.stage (p + 1)).arrow
        (𝟙 _) (X.filtration.stage p).arrow
        (by rw [DecreasingFiltration.succInclusion_arrow, Category.id_comp])
    let q (X : FilteredObject C) : X.quotient (p + 1) ⟶ X.quotient p :=
      cokernel.map (X.filtration.stage (p + 1)).arrow (X.filtration.stage p).arrow
        (X.filtration.succInclusion p) (𝟙 _)
        (by rw [DecreasingFiltration.succInclusion_arrow, Category.comp_id])
    have w (X : FilteredObject C) : i X ≫ q X = 0 := by
      apply (cancel_epi (cokernel.π (X.filtration.succInclusion p))).1
      simp only [i, q, cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc, Category.id_comp,
        cokernel.condition, comp_zero]
    have row (X : FilteredObject C) : (ShortComplex.mk (i X) (q X) (w X)).ShortExact := by
      exact cokernel_extension_shortExact (X.filtration.succInclusion p)
        (X.filtration.stage p).arrow (X.filtration.stage (p + 1)).arrow
        (DecreasingFiltration.succInclusion_arrow X.filtration p)
    have hi {X Y : FilteredObject C} (f : X ⟶ Y) :
        i X ≫ f.quotientMap (p + 1) = f.gradedPieceMap p ≫ i Y := by
      apply (cancel_epi (cokernel.π (X.filtration.succInclusion p))).1
      simp only [i, Hom.gradedPieceMap, Hom.quotientMap, cokernel.π_desc_assoc,
        cokernel.π_desc, Category.assoc]
      rw [← Category.assoc (f.stageMap p), f.stageMap_arrow p, Category.assoc]
    have hq {X Y : FilteredObject C} (f : X ⟶ Y) :
        q X ≫ f.quotientMap p = f.quotientMap (p + 1) ≫ q Y := by
      apply (cancel_epi (cokernel.π (X.filtration.stage (p + 1)).arrow)).1
      simp only [q, Hom.quotientMap, cokernel.π_desc_assoc, cokernel.π_desc,
        Category.id_comp, Category.assoc]
    let α : S.map (associatedGradedFunctor ⋙ GradedObject.eval p) ⟶
        S.map (quotientFunctor (p + 1)) :=
      homMk (i S.X₁) (i S.X₂) (i S.X₃) (hi S.f) (hi S.g)
    let β : S.map (quotientFunctor (p + 1)) ⟶ S.map (quotientFunctor p) :=
      homMk (q S.X₁) (q S.X₂) (q S.X₃) (hq S.f) (hq S.g)
    haveI : Mono α.τ₂ := (row S.X₂).mono_f
    haveI : Mono α.τ₃ := (row S.X₃).mono_f
    haveI : Epi β.τ₁ := (row S.X₁).epi_g
    exact exact_of_extension α β (w S.X₂) (row S.X₂).exact (exact_piece hgr p) hs
  obtain ⟨n, m, hn, hm⟩ := hX₂fin
  have base (k : ℤ) (hkn : k ≤ n) : (S.map (quotientFunctor k)).Exact := by
    have hk : S.X₂.filtration.stage k = ⊤ :=
      top_unique (hn ▸ S.X₂.filtration.antitone hkn)
    haveI : IsIso (S.X₂.filtration.stage k).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 hk
    exact exact_of_isZero_X₂ _ (isZero_cokernel_of_epi _)
  refine Int.inductionOn' p n (base n le_rfl) (fun k _ ih ↦ step k ih)
    (fun k hkn _ ↦ base (k - 1) (by omega))

/-- For finite filtrations, associated-graded exactness forces the first differential to be
strict. -/
@[stacks 05QH]
theorem strict_f
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) : Strict S.f :=
  strict_f_of_stages (exact_stage hX₁fin hX₂fin hX₃fin hgr)

/-- For finite filtrations, associated-graded exactness forces the second differential to be
strict. -/
@[stacks 05QH]
theorem strict_g
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) : Strict S.g :=
  strict_g_of_quotients (exact_quotient hX₁fin hX₂fin hX₃fin hgr)

/-- For finite filtrations, associated-graded exactness implies exactness of the underlying short
complex. -/
@[stacks 05QH]
theorem exact_underlying
    (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
    (hgr : (S.map associatedGradedFunctor).Exact) :
    (S.map FilteredObject.forget).Exact :=
  exact_underlying_of_stages hX₁fin hX₂fin (exact_stage hX₁fin hX₂fin hX₃fin hgr)

end AssociatedGraded

namespace Exact

/-- Exactness on every stage together with underlying exactness forces the first differential to
be strict. -/
theorem strict_f_of_stage
    (hunder : (S.map FilteredObject.forget).Exact)
    (hstage : ∀ p : ℤ, (S.map (Stage.functor p)).Exact) : Strict S.f :=
  strict_f_of_stages hstage

/-- Exactness after every filtration quotient forces the second differential to be strict. -/
theorem strict_g_of_quotient
    (hquot : ∀ p : ℤ, (S.map (quotientFunctor p)).Exact) : Strict S.g :=
  strict_g_of_quotients hquot

end Exact

end Filtered

end CategoryTheory.ShortComplex
