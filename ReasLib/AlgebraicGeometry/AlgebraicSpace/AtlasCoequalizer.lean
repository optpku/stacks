/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Functor.RegularEpi
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Atlas kernel-pair coequalizers

This module records the sheaf morphism, cofork, and relation properties associated to a
representable étale atlas of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

private theorem atlasKernelPair_t {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    (kernelPair f hf).t = hf.fst' f := by
  change prod.lift (hf.fst' f) (hf.snd f) ≫ prod.fst = hf.fst' f
  exact prod.lift_fst _ _

private theorem atlasKernelPair_s {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) (hf : yoneda.relativelyRepresentable f) :
    (kernelPair f hf).s = hf.snd f := by
  change prod.lift (hf.fst' f) (hf.snd f) ≫ prod.snd = hf.snd f
  exact prod.lift_snd _ _

private theorem atlasKernelPair_isKernelPair {S : Scheme.{u}} {F : AlgebraicSpace S}
    {U : Over S} (f : yoneda.obj U ⟶ F.functorOfPoints)
    (hf : yoneda.relativelyRepresentable f) :
    IsKernelPair f (yoneda.map (kernelPair f hf).t) (yoneda.map (kernelPair f hf).s) := by
  rw [atlasKernelPair_t, atlasKernelPair_s]
  exact hf.isPullback' f

/-- The morphism of small-valued fppf sheaves associated to a map from a scheme to an algebraic
space. -/
def sheafHom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) :
    (Scheme.fppfTopology.over S).yoneda.obj U ⟶ toSmallSheaf F :=
  Sheaf.homEquiv.symm f

/-- The underlying presheaf morphism of `sheafHom f` is `f`. -/
theorem sheafHom_hom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) :
    (sheafHom f).hom = f := rfl

/-- The two sheafified projections of the kernel pair equalize `sheafHom f`. -/
theorem sheafHom_equalizes {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    (Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).t ≫ sheafHom f =
      (Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).s ≫
        sheafHom f := by
  apply (sheafToPresheaf _ _).map_injective
  change yoneda.map (kernelPair f h_etale.rep).t ≫ f =
    yoneda.map (kernelPair f h_etale.rep).s ≫ f
  exact (atlasKernelPair_isKernelPair f h_etale.rep).w

/-- The diagram `R ⇉ U ⟶ F` in the category of small-valued fppf sheaves on `Sch/S`. -/
def cofork {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Cofork ((Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).t)
      ((Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).s) :=
  Cofork.ofπ (sheafHom f) (sheafHom_equalizes f h_etale)

/-- The coequalizer candidate of `cofork f h_etale` is `sheafHom f`. -/
theorem cofork_π {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    (cofork f h_etale).π = sheafHom f := rfl

/-- An étale-locally surjective atlas remains locally surjective as a morphism of fppf sheaves. -/
instance instIsLocallySurjective_sheafHom {S : Scheme.{u}} {F : AlgebraicSpace S}
    {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    [h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f] :
    Sheaf.IsLocallySurjective (sheafHom f) := by
  have h : Scheme.etaleTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono
      (Scheme.precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)
  have h_over : Scheme.etaleTopology.over S ≤ Scheme.fppfTopology.over S := by
    intro T R hR
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact h _ hR
  change Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f
  exact Presheaf.isLocallySurjective_of_le h_over f h_surj

/-- The kernel pair of a representable étale atlas is an internal equivalence relation. -/
instance isEquivalenceRelation {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    IsEquivalenceRelation (kernelPair f h_etale.rep).t (kernelPair f h_etale.rep).s := by
  rw [atlasKernelPair_t, atlasKernelPair_s]
  let hf := h_etale.rep
  have hw := (hf.isPullback' f).w
  have htrans :
      yoneda.map (pullback.fst (hf.snd f) (hf.fst' f) ≫ hf.fst' f) ≫ f =
        yoneda.map (pullback.snd (hf.snd f) (hf.fst' f) ≫ hf.snd f) ≫ f := by
    calc
      yoneda.map (pullback.fst (hf.snd f) (hf.fst' f) ≫ hf.fst' f) ≫ f =
          yoneda.map (pullback.fst (hf.snd f) (hf.fst' f) ≫ hf.snd f) ≫ f := by
            simp only [Functor.map_comp, Category.assoc, hw]
      _ = yoneda.map (pullback.snd (hf.snd f) (hf.fst' f) ≫ hf.fst' f) ≫ f := by
            rw [pullback.condition]
      _ = yoneda.map (pullback.snd (hf.snd f) (hf.fst' f) ≫ hf.snd f) ≫ f := by
            simp only [Functor.map_comp, Category.assoc, hw]
  exact ⟨⟨{
    right_cancellation := fun _ a b h₁ h₂ ↦ hf.hom_ext' h₁ h₂
    r := hf.lift' (𝟙 U) (𝟙 U) rfl
    reflexivity₁ := hf.lift'_fst _ _ _
    reflexivity₂ := hf.lift'_snd _ _ _
    s := hf.lift' (hf.snd f) (hf.fst' f) hw.symm
    symmetry₁ := hf.lift'_fst _ _ _
    symmetry₂ := hf.lift'_snd _ _ _
    c := pullback.cone (hf.snd f) (hf.fst' f)
    isLimit := pullback.isLimit _ _
    t := hf.lift' (pullback.fst (hf.snd f) (hf.fst' f) ≫ hf.fst' f)
      (pullback.snd (hf.snd f) (hf.fst' f) ≫ hf.snd f) htrans
    transitivity₁ := hf.lift'_fst _ _ _
    transitivity₂ := hf.lift'_snd _ _ _
  }⟩⟩

/-- The two projections of the kernel pair of a representable étale atlas are étale. -/
theorem etale_projections {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Etale (kernelPair f h_etale.rep).t.left ∧ Etale (kernelPair f h_etale.rep).s.left := by
  rw [atlasKernelPair_t, atlasKernelPair_s]
  exact ⟨h_etale.property f (yoneda.map (h_etale.rep.snd f)) (h_etale.rep.fst' f)
    (h_etale.rep.isPullback' f).flip, h_etale.property_snd f⟩

/-- The first projection of the kernel pair of a representable étale atlas is étale. -/
instance instEtale_kernelPair_t {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Etale (kernelPair f h_etale.rep).t.left :=
  (etale_projections f h_etale).1

/-- The second projection of the kernel pair of a representable étale atlas is étale. -/
instance instEtale_kernelPair_s {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Etale (kernelPair f h_etale.rep).s.left :=
  (etale_projections f h_etale).2

/-- The kernel pair of a representable étale atlas is an étale equivalence relation. -/
instance instIsEtaleEquivalenceRelation_kernelPair {S : Scheme.{u}} {F : AlgebraicSpace S}
    {U : Over S} (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    (kernelPair f h_etale.rep).IsEtaleEquivalenceRelation :=
  ⟨isEquivalenceRelation f h_etale, instEtale_kernelPair_t f h_etale,
    instEtale_kernelPair_s f h_etale⟩

/-- The atlas cofork is a coequalizer in the category of small-valued fppf sheaves. -/
theorem isCoequalizer {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    Nonempty (IsColimit (cofork f h_etale)) := by
  letI := h_surj
  haveI : IsIso (Sheaf.imageι (sheafHom f)) :=
    (Sheaf.isLocallySurjective_iff_isIso (sheafHom f)).mp inferInstance
  let imageIso : Sheaf.image (sheafHom f) ≅ toSmallSheaf F :=
    asIso (Sheaf.imageι (sheafHom f))
  have hk : IsKernelPair (Subfunctor.toRange f) (yoneda.map (kernelPair f h_etale.rep).t)
      (yoneda.map (kernelPair f h_etale.rep).s) := by
    apply IsKernelPair.cancel_right_of_mono (f₂ := (Subfunctor.range f).ι)
    simpa only [Subfunctor.toRange_ι] using atlasKernelPair_isKernelPair f h_etale.rep
  -- First descend to the presheaf image, then extend across its sheaf closure.
  -- This works for small-valued sheaves without assuming small-valued sheafification exists.
  let hc := hk.toCoequalizer (regularEpiOfEpi (Subfunctor.toRange f))
  refine ⟨Cofork.IsColimit.mk' (cofork f h_etale) (fun c ↦ ?_)⟩
  have hπ : yoneda.map (kernelPair f h_etale.rep).t ≫ c.π.hom =
      yoneda.map (kernelPair f h_etale.rep).s ≫ c.π.hom :=
    (sheafToPresheaf _ _).congr_map c.condition
  let d := Cofork.IsColimit.desc hc c.π.hom hπ
  have hd : Subfunctor.toRange f ≫ d = c.π.hom :=
    Cofork.IsColimit.π_desc' hc c.π.hom hπ
  have hH : Presieve.IsSheaf (Scheme.fppfTopology.over S) c.pt.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp c.pt.property
  let e : Sheaf.image (sheafHom f) ⟶ c.pt :=
    Sheaf.homEquiv.symm ((Subfunctor.range f).sheafifyLift d hH)
  have he : Sheaf.toImage (sheafHom f) ≫ e = c.π := by
    apply Sheaf.hom_ext
    change (Subfunctor.toRange f ≫ Subfunctor.homOfLe _) ≫
      (Subfunctor.range f).sheafifyLift d hH = c.π.hom
    rw [Category.assoc, Subfunctor.to_sheafifyLift]
    exact hd
  have hl : (cofork f h_etale).π ≫ imageIso.inv ≫ e = c.π := by
    change sheafHom f ≫ imageIso.inv ≫ e = c.π
    calc
      sheafHom f ≫ imageIso.inv ≫ e =
          (Sheaf.toImage (sheafHom f) ≫ imageIso.hom) ≫ imageIso.inv ≫ e :=
        congrArg (fun k ↦ k ≫ imageIso.inv ≫ e) (Sheaf.toImage_ι (sheafHom f)).symm
      _ = Sheaf.toImage (sheafHom f) ≫ e := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = c.π := he
  exact ⟨imageIso.inv ≫ e, hl,
    fun {m} hm ↦ (cancel_epi (sheafHom f)).mp (hm.trans hl.symm)⟩

end AlgebraicGeometry.AlgebraicSpace
