/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of a site at a set-valued presheaf

The localization site `C / G` is the opposite category of elements of `G`, equipped with the
restricted topology of the elements projection. Sheafification of `G` induces a relocalization
functor whose sheaf pushforward identifies `Sh(C / G)` with the localization of `Sh(C)` at `G#`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u z z'

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The projection `j : C / G ⥤ C` from the opposite category of elements of a type-valued
presheaf. -/
abbrev localizationForget (G : Cᵒᵖ ⥤ Type (max w v)) : G.Elementsᵒᵖ ⥤ C :=
  (CategoryOfElements.π G).leftOp

/-- The localization site `C / G` is the opposite category of elements of `G` with the
restricted topology of `localizationForget`. -/
abbrev localizationSite (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Type (max w v)) :
    GrothendieckTopology G.Elementsᵒᵖ :=
  (localizationForget G).restrictedTopology J

private theorem localizationForget_mem_pushforward
    (G : Cᵒᵖ ⥤ Type (max w v)) {X Y : G.Elementsᵒᵖ} (S : Sieve X) (f : Y ⟶ X) :
    S.functorPushforward (localizationForget G) ((localizationForget G).map f) ↔ S f := by
  constructor
  · rintro ⟨Z, g, h, hg, heq⟩
    let k : Y ⟶ Z := (CategoryOfElements.homMk _ _ h.op (by
      change G.map h.op Z.unop.snd = Y.unop.snd
      calc
        G.map h.op Z.unop.snd = G.map h.op (G.map g.unop.val X.unop.snd) :=
          congrArg (G.map h.op) g.unop.property.symm
        _ = G.map (h ≫ (localizationForget G).map g).op X.unop.snd :=
          (G.map_comp_apply _ _ _).symm
        _ = G.map f.unop.val X.unop.snd :=
          congrArg (fun k ↦ G.map k.op X.unop.snd) heq.symm
        _ = Y.unop.snd := f.unop.property)).op
    have hk : k ≫ g = f := by
      apply (localizationForget G).map_injective
      exact heq.symm
    simpa only [hk] using S.downward_closed hg k
  · exact Sieve.image_mem_functorPushforward _ _

private theorem localizationForget_pushforward_functorPullback
    (G : Cᵒᵖ ⥤ Type (max w v)) {X : G.Elementsᵒᵖ}
    (S : Sieve ((localizationForget G).obj X)) :
    (S.functorPullback (localizationForget G)).functorPushforward (localizationForget G) = S := by
  apply le_antisymm (Sieve.functorPullback_pushforward_le _ _)
  intro Y f hf
  let Y' : G.Elementsᵒᵖ := op ⟨op Y, G.map f.op X.unop.snd⟩
  let f' : Y' ⟶ X := (CategoryOfElements.homMk _ _ f.op rfl).op
  exact ⟨Y', f', 𝟙 Y, hf, (Category.id_comp f).symm⟩

private theorem localizationForget_functorPullback_pushforward
    (G : Cᵒᵖ ⥤ Type (max w v)) {X : G.Elementsᵒᵖ} (S : Sieve X) :
    (S.functorPushforward (localizationForget G)).functorPullback (localizationForget G) = S := by
  ext Y f
  exact localizationForget_mem_pushforward G S f

private theorem localizationForget_pushforward_pullback
    (G : Cᵒᵖ ⥤ Type (max w v)) {X Y : G.Elementsᵒᵖ} (S : Sieve X) (f : Y ⟶ X) :
    (S.pullback f).functorPushforward (localizationForget G) =
      (S.functorPushforward (localizationForget G)).pullback ((localizationForget G).map f) := by
  have hinj : Function.Injective (fun T : Sieve ((localizationForget G).obj Y) ↦
      T.functorPullback (localizationForget G)) := by
    intro T R h
    exact (localizationForget_pushforward_functorPullback G T).symm.trans
      ((congrArg (Sieve.functorPushforward (localizationForget G)) h).trans
        (localizationForget_pushforward_functorPullback G R))
  apply hinj
  dsimp only
  rw [localizationForget_functorPullback_pushforward G, Sieve.functorPullback_pullback,
    localizationForget_functorPullback_pushforward G]

/-- A sieve covers on `C / G` exactly when its image under `localizationForget` covers in `J`. -/
theorem mem_localizationSite_iff (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Type (max w v))
    {X : G.Elementsᵒᵖ} {S : Sieve X} :
    S ∈ localizationSite J G X ↔
      S.functorPushforward (localizationForget G) ∈ J ((localizationForget G).obj X) := by
  constructor
  · intro hS
    change (Precoverage.comap (localizationForget G) J.toPrecoverage).Saturate X S at hS
    induction hS with
    | of X R hR =>
        simpa only [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
          Sieve.generate_map_eq_functorPushforward] using hR
    | top X => simpa using J.top_mem ((localizationForget G).obj X)
    | pullback X S _ Y f ih =>
        rw [localizationForget_pushforward_pullback]
        exact J.pullback_stable _ ih
    | transitive X S R _ _ ihS ihR =>
        apply J.transitive ihS (R.functorPushforward (localizationForget G))
        rintro Y f ⟨Z, g, h, hg, rfl⟩
        have hh := J.pullback_stable h (ihR hg)
        rw [localizationForget_pushforward_pullback] at hh
        simpa only [← Sieve.pullback_comp] using hh
  · exact (localizationForget G).mem_restrictedTopology_of_functorPushforward_mem

/-- The elements projection is continuous for `localizationSite`. -/
instance localizationForget_isContinuous (J : GrothendieckTopology C)
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsContinuous (localizationForget G) (localizationSite J G) J := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
    let W : G.Elementsᵒᵖ :=
      op ⟨op X, G.map (f₁ ≫ (localizationForget G).map g₁).op Z.unop.snd⟩
    let a : W ⟶ Y₁ := (CategoryOfElements.homMk _ _ f₁.op (by
      change G.map f₁.op Y₁.unop.snd =
        G.map (f₁ ≫ (localizationForget G).map g₁).op Z.unop.snd
      exact (congrArg (G.map f₁.op) g₁.unop.property.symm).trans
        (G.map_comp_apply _ _ _).symm)).op
    let b : W ⟶ Y₂ := (CategoryOfElements.homMk _ _ f₂.op (by
      change G.map f₂.op Y₂.unop.snd =
        G.map (f₁ ≫ (localizationForget G).map g₁).op Z.unop.snd
      exact ((congrArg (G.map f₂.op) g₂.unop.property.symm).trans
        (G.map_comp_apply _ _ _).symm).trans
          (congrArg (fun k ↦ G.map k.op Z.unop.snd) heq.symm))).op
    exact hx a b hg₁ hg₂ ((localizationForget G).map_injective heq)
  · exact ⟨(mem_localizationSite_iff J G).mp⟩

/-- The elements projection is cocontinuous for `localizationSite`. -/
instance localizationForget_isCocontinuous (J : GrothendieckTopology C)
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsCocontinuous (localizationForget G) (localizationSite J G) J where
  cover_lift hS := by
    rw [mem_localizationSite_iff, localizationForget_pushforward_functorPullback]
    exact hS

/-- Fibre products on `C` yield fibre products on `C / G`. -/
instance hasPullbacks_elementsOp (G : Cᵒᵖ ⥤ Type (max w v)) [HasPullbacks C] :
    HasPullbacks G.Elementsᵒᵖ := by
  refine @hasPullbacks_of_hasLimit_cospan _ _ ?_
  intro X Y Z f g
  let F := localizationForget G
  let P : G.Elementsᵒᵖ :=
    op ⟨op (pullback (F.map f) (F.map g)),
      G.map (pullback.fst (F.map f) (F.map g)).op X.unop.snd⟩
  let p₁ : P ⟶ X :=
    (CategoryOfElements.homMk _ _ (pullback.fst (F.map f) (F.map g)).op rfl).op
  let p₂ : P ⟶ Y :=
    (CategoryOfElements.homMk _ _ (pullback.snd (F.map f) (F.map g)).op (by
      change G.map (pullback.snd (F.map f) (F.map g)).op Y.unop.snd =
        G.map (pullback.fst (F.map f) (F.map g)).op X.unop.snd
      calc
        _ = G.map (pullback.snd (F.map f) (F.map g) ≫ F.map g).op Z.unop.snd :=
          (congrArg (G.map (pullback.snd (F.map f) (F.map g)).op) g.unop.property.symm).trans
            (G.map_comp_apply _ _ _).symm
        _ = G.map (pullback.fst (F.map f) (F.map g) ≫ F.map f).op Z.unop.snd :=
          congrArg (fun k : pullback (F.map f) (F.map g) ⟶ F.obj Z ↦
            G.map k.op Z.unop.snd) (pullback.condition (f := F.map f) (g := F.map g)).symm
        _ = _ := (G.map_comp_apply _ _ _).trans
          (congrArg (G.map (pullback.fst (F.map f) (F.map g)).op) f.unop.property))).op
  have hp : p₁ ≫ f = p₂ ≫ g := F.map_injective pullback.condition
  refine HasLimit.mk ⟨PullbackCone.mk p₁ p₂ hp, PullbackCone.IsLimit.mk hp ?_ ?_ ?_ ?_⟩
  · intro s
    let l := pullback.lift (F.map s.fst) (F.map s.snd) (F.congr_map s.condition)
    exact (CategoryOfElements.homMk _ _ l.op (by
      change G.map l.op (G.map (pullback.fst (F.map f) (F.map g)).op X.unop.snd) = _
      exact (G.map_comp_apply _ _ _).symm.trans
        ((congrArg (fun k : F.obj s.pt ⟶ F.obj X ↦ G.map k.op X.unop.snd)
          (pullback.lift_fst (F.map s.fst) (F.map s.snd) (F.congr_map s.condition))).trans
            s.fst.unop.property))).op
  · intro s
    apply F.map_injective
    exact pullback.lift_fst _ _ _
  · intro s
    apply F.map_injective
    exact pullback.lift_snd _ _ _
  · intro s m h₁ h₂
    apply F.map_injective
    apply pullback.hom_ext
    · exact (F.congr_map h₁).trans (pullback.lift_fst _ _ _).symm
    · exact (F.congr_map h₂).trans (pullback.lift_snd _ _ _).symm

/-- Equalizers on `C` yield equalizers on `C / G`. -/
instance hasEqualizers_elementsOp (G : Cᵒᵖ ⥤ Type (max w v)) [HasEqualizers C] :
    HasEqualizers G.Elementsᵒᵖ := by
  refine @hasEqualizers_of_hasLimit_parallelPair _ _ ?_
  intro X Y f g
  let F := localizationForget G
  let E : G.Elementsᵒᵖ :=
    op ⟨op (equalizer (F.map f) (F.map g)),
      G.map (equalizer.ι (F.map f) (F.map g)).op X.unop.snd⟩
  let ι : E ⟶ X :=
    (CategoryOfElements.homMk _ _ (equalizer.ι (F.map f) (F.map g)).op rfl).op
  have hι : ι ≫ f = ι ≫ g := F.map_injective (equalizer.condition (F.map f) (F.map g))
  refine HasLimit.mk ⟨Fork.ofι ι hι, Fork.IsLimit.mk _ ?_ ?_ ?_⟩
  · intro s
    let l := equalizer.lift (F.map s.ι) (F.congr_map s.condition)
    exact (CategoryOfElements.homMk _ _ l.op (by
      change G.map l.op (G.map (equalizer.ι (F.map f) (F.map g)).op X.unop.snd) = _
      exact (G.map_comp_apply _ _ _).symm.trans
        ((congrArg (fun k : F.obj s.pt ⟶ F.obj X ↦ G.map k.op X.unop.snd)
          (equalizer.lift_ι (F.map s.ι) (F.congr_map s.condition))).trans s.ι.unop.property))).op
  · intro s
    apply F.map_injective
    exact equalizer.lift_ι _ _
  · intro s m hm
    apply F.map_injective
    apply equalizer.hom_ext
    exact (F.congr_map hm).trans (equalizer.lift_ι _ _).symm

variable (J : GrothendieckTopology C)

/-- Inverse image along `j : C / G ⥤ C`. -/
abbrev elementsOpInverseImage (G : Cᵒᵖ ⥤ Type (max w v)) (A : Type z) [Category.{z'} A] :
    Sheaf J A ⥤ Sheaf (localizationSite J G) A :=
  (localizationForget G).sheafPushforwardContinuous A (localizationSite J G) J

variable [HasWeakSheafify J (Type (max w v))]

/-- The site functor `C / G ⥤ C / G#` induced by the sheafification unit of `G`. -/
def sheafificationRelocalization (G : Cᵒᵖ ⥤ Type (max w v)) :
    G.Elementsᵒᵖ ⥤ ((presheafToSheaf J (Type (max w v))).obj G).obj.Elementsᵒᵖ :=
  (CategoryOfElements.map (toSheafify J G)).op

/-- Relocalization along sheafification commutes with the projections to `C`. -/
theorem sheafificationRelocalization_comp_projection (G : Cᵒᵖ ⥤ Type (max w v)) :
    sheafificationRelocalization J G ⋙
        localizationForget ((presheafToSheaf J (Type (max w v))).obj G).obj =
      localizationForget G :=
  rfl

private theorem elementsMap_compatiblePreserving
    {G H : Cᵒᵖ ⥤ Type (max w v)} (α : G ⟶ H)
    (K : GrothendieckTopology H.Elementsᵒᵖ) :
    CompatiblePreserving.{z} K (CategoryOfElements.map α).op := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
  let F := (CategoryOfElements.map α).op
  have heq' : g₁.unop.val ≫ f₁.unop.val = g₂.unop.val ≫ f₂.unop.val :=
    congrArg (fun k ↦ k.unop.val) heq
  let W : G.Elementsᵒᵖ := op ⟨X.unop.fst, G.map f₁.unop.val Y₁.unop.snd⟩
  let a : W ⟶ Y₁ := (CategoryOfElements.homMk (F := G) Y₁.unop W.unop f₁.unop.val rfl).op
  let b : W ⟶ Y₂ := (CategoryOfElements.homMk (F := G) Y₂.unop W.unop f₂.unop.val (by
    change G.map f₂.unop.val Y₂.unop.snd = G.map f₁.unop.val Y₁.unop.snd
    calc
      _ = G.map (g₂.unop.val ≫ f₂.unop.val) Z.unop.snd :=
        (congrArg (G.map f₂.unop.val) g₂.unop.property.symm).trans
          (G.map_comp_apply _ _ _).symm
      _ = G.map (g₁.unop.val ≫ f₁.unop.val) Z.unop.snd :=
        congrArg (fun k ↦ G.map k Z.unop.snd) heq'.symm
      _ = _ := (G.map_comp_apply _ _ _).trans
        (congrArg (G.map f₁.unop.val) g₁.unop.property))).op
  have hab : a ≫ g₁ = b ≫ g₂ := by
    apply Quiver.Hom.unop_inj
    exact Subtype.ext heq'
  let e : X ≅ F.obj W :=
    (CategoryOfElements.isoMk (F := H) (F.obj W).unop X.unop (Iso.refl X.unop.fst) (by
      change H.map (𝟙 _) (α.app X.unop.fst (G.map f₁.unop.val Y₁.unop.snd)) = X.unop.snd
      exact (H.map_id_apply _ _).trans
        ((α.naturality_apply f₁.unop.val Y₁.unop.snd).trans f₁.unop.property))).op
  have ha : e.hom ≫ F.map a = f₁ := by
    apply (localizationForget H).map_injective
    exact Category.id_comp _
  have hb : e.hom ≫ F.map b = f₂ := by
    apply (localizationForget H).map_injective
    exact Category.id_comp _
  have hh := congrArg (fun t ↦ ℱ.obj.map e.hom.op t) (hx a b hg₁ hg₂ hab)
  change ℱ.obj.map e.hom.op (ℱ.obj.map (F.map a).op (x g₁ hg₁)) =
    ℱ.obj.map e.hom.op (ℱ.obj.map (F.map b).op (x g₂ hg₂)) at hh
  have h₁ : ℱ.obj.map e.hom.op (ℱ.obj.map (F.map a).op (x g₁ hg₁)) =
      ℱ.obj.map f₁.op (x g₁ hg₁) :=
    (ℱ.obj.map_comp_apply _ _ _).symm.trans
      (congrArg (fun k ↦ ℱ.obj.map k.op (x g₁ hg₁)) ha)
  have h₂ : ℱ.obj.map e.hom.op (ℱ.obj.map (F.map b).op (x g₂ hg₂)) =
      ℱ.obj.map f₂.op (x g₂ hg₂) :=
    (ℱ.obj.map_comp_apply _ _ _).symm.trans
      (congrArg (fun k ↦ ℱ.obj.map k.op (x g₂ hg₂)) hb)
  exact h₁.symm.trans (hh.trans h₂)

/-- Sheafification relocalization is continuous for the two localization topologies. -/
instance sheafificationRelocalization_isContinuous (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsContinuous (sheafificationRelocalization J G)
      (localizationSite J G)
      (localizationSite J ((presheafToSheaf J (Type (max w v))).obj G).obj) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact elementsMap_compatiblePreserving _ _
  · constructor
    intro X S hS
    apply (mem_localizationSite_iff J
      ((presheafToSheaf J (Type (max w v))).obj G).obj).mpr
    change (S.functorPushforward (sheafificationRelocalization J G)).functorPushforward
      (localizationForget ((presheafToSheaf J (Type (max w v))).obj G).obj) ∈
        J ((localizationForget G).obj X)
    rw [← Sieve.functorPushforward_comp]
    exact (mem_localizationSite_iff J G).mp hS

/-- Sheafification relocalization is cocontinuous for the two localization topologies. -/
instance sheafificationRelocalization_isCocontinuous (G : Cᵒᵖ ⥤ Type (max w v)) :
    Functor.IsCocontinuous (sheafificationRelocalization J G)
      (localizationSite J G)
      (localizationSite J ((presheafToSheaf J (Type (max w v))).obj G).obj) where
  cover_lift {U} {S} hS := by
    have h := (localizationForget G).cover_lift (localizationSite J G) J (U := U)
      ((mem_localizationSite_iff J
        ((presheafToSheaf J (Type (max w v))).obj G).obj).mp hS)
    have heq :
        (S.functorPushforward
          (localizationForget ((presheafToSheaf J (Type (max w v))).obj G).obj)).functorPullback
            (X := U) (localizationForget G) =
              S.functorPullback (X := U) (sheafificationRelocalization J G) := by
      exact (Sieve.functorPullback_comp (X := U) (sheafificationRelocalization J G)
        (localizationForget ((presheafToSheaf J (Type (max w v))).obj G).obj) _).trans
          (congrArg (Sieve.functorPullback (sheafificationRelocalization J G))
            (localizationForget_functorPullback_pushforward
              ((presheafToSheaf J (Type (max w v))).obj G).obj
              (X := (sheafificationRelocalization J G).obj U) S))
    rwa [heq] at h

/-- Sheaf pushforward along sheafification relocalization is an equivalence, so
`Sh(C / G)` identifies with the localization of `Sh(C)` at `G#`. -/
instance sheafificationRelocalization_sheafPushforward_isEquivalence
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    ((sheafificationRelocalization J G).sheafPushforwardContinuous (Type (max w v))
        (localizationSite J G)
        (localizationSite J
          ((presheafToSheaf J (Type (max w v))).obj G).obj)).IsEquivalence :=
  sorry

end CategoryTheory.Presheaf
