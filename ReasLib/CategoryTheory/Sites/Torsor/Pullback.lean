/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Torsor.IsoClasses

/-!
# Inverse image of torsors on sites

The inverse image of a torsor is obtained by transporting its sheaf action
through the product and coefficient comparisons for sheaf inverse image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The sectionwise action of a torsor commutes with restriction on the product sheaf. -/
theorem action_naturality {G : Sheaf J GrpCat.{w}} (P : Torsor G)
    {U V : Cᵒᵖ} (h : U ⟶ V) :
    ((sheafForget J).obj G ⨯ P.carrier).obj.map h ≫
        TypeCat.ofHom (fun p ↦ (P.mulAction V.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app V p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
            P.carrier).hom.app V p)) =
      TypeCat.ofHom (fun p ↦ (P.mulAction U.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app U p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
            P.carrier).hom.app U p)) ≫ P.carrier.obj.map h := by
  apply ConcreteCategory.hom_ext
  intro p
  have hfst := ConcreteCategory.congr_hom
    ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
      (sheafForget J).obj G).hom.naturality h) p
  have hsnd := ConcreteCategory.congr_hom
    ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
      P.carrier).hom.naturality h) p
  dsimp at hfst hsnd ⊢
  rw [hfst, hsnd]
  exact (P.act_naturality h.unop _ _).symm

/-- The action of a group sheaf on a torsor, as a morphism of sheaves of sets. -/
def action {G : Sheaf J GrpCat.{w}} (P : Torsor G) :
    (sheafForget J).obj G ⨯ P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun U ↦ TypeCat.ofHom fun p ↦
        (P.mulAction U.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app U p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
            P.carrier).hom.app U p)
      naturality := fun {_ _} h ↦ action_naturality P h }

variable (K)
variable (f : C ⥤ D) [f.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ Type w, f.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ GrpCat.{w}, f.op.HasLeftKanExtension P]
variable [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
variable [J.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
variable [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
variable [(CategoryTheory.forget GrpCat.{w}).PreservesLeftKanExtensions f.op]
variable [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})]
variable [hLeftExact : PreservesFiniteLimits (f.sheafPullback (Type w) J K)]

/-- Inverse image transports the action through the product and coefficient comparisons. -/
def pullbackAction (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G) ⨯
        (f.sheafPullback (Type w) J K).obj P.carrier ⟶
      (f.sheafPullback (Type w) J K).obj P.carrier :=
  prod.map
      ((Functor.sheafPullback.compSheafComposeIso f
        (CategoryTheory.forget GrpCat.{w}) J K).app G).hom (𝟙 _) ≫
    (PreservesLimitPair.iso (f.sheafPullback (Type w) J K)
      ((sheafForget J).obj G) P.carrier).inv ≫
    (f.sheafPullback (Type w) J K).map (action P)

set_option backward.privateInPublic true in
private def prodSection (A B : Sheaf K (Type w)) {U : Dᵒᵖ}
    (a : A.obj.obj U) (b : B.obj.obj U) : (A ⨯ B).obj.obj U :=
  (PreservesLimitPair.iso (sheafToPresheaf K (Type w)) A B).inv.app U
    (FunctorToTypes.prodMk a b)

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_fst (A B : Sheaf K (Type w)) {U : Dᵒᵖ}
    (a : A.obj.obj U) (b : B.obj.obj U) :
    (prod.fst : A ⨯ B ⟶ A).hom.app U (prodSection K A B a b) = a := by
  have h := congrArg (fun k ↦ k.app U (FunctorToTypes.prodMk a b))
    (PreservesLimitPair.iso_inv_fst (sheafToPresheaf K (Type w)) A B)
  exact h.trans (FunctorToTypes.prodMk_fst a b)

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_snd (A B : Sheaf K (Type w)) {U : Dᵒᵖ}
    (a : A.obj.obj U) (b : B.obj.obj U) :
    (prod.snd : A ⨯ B ⟶ B).hom.app U (prodSection K A B a b) = b := by
  have h := congrArg (fun k ↦ k.app U (FunctorToTypes.prodMk a b))
    (PreservesLimitPair.iso_inv_snd (sheafToPresheaf K (Type w)) A B)
  exact h.trans (FunctorToTypes.prodMk_snd a b)

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_ext (A B : Sheaf K (Type w)) {U : Dᵒᵖ}
    (x y : (A ⨯ B).obj.obj U)
    (hf : (prod.fst : A ⨯ B ⟶ A).hom.app U x =
      (prod.fst : A ⨯ B ⟶ A).hom.app U y)
    (hs : (prod.snd : A ⨯ B ⟶ B).hom.app U x =
      (prod.snd : A ⨯ B ⟶ B).hom.app U y) : x = y := by
  let E := sheafToPresheaf K (Type w) ⋙
    (CategoryTheory.evaluation Dᵒᵖ (Type w)).obj U
  have h : (TypeCat.ofHom (fun _ : PUnit.{w + 1} ↦ x) : PUnit.{w + 1} ⟶ E.obj (A ⨯ B)) =
      TypeCat.ofHom (fun _ : PUnit.{w + 1} ↦ y) := by
    apply BinaryFan.IsLimit.hom_ext (isLimitOfHasBinaryProductOfPreservesLimit E A B)
    · apply ConcreteCategory.hom_ext
      intro _
      exact hf
    · apply ConcreteCategory.hom_ext
      intro _
      exact hs
  exact ConcreteCategory.congr_hom h PUnit.unit

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_map {A B A' B' : Sheaf K (Type w)}
    (a : A ⟶ A') (b : B ⟶ B') {U : Dᵒᵖ} (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.map a b).hom.app U (prodSection K A B x y) =
      prodSection K A' B' (a.hom.app U x) (b.hom.app U y) := by
  apply prodSection_ext
  · have h := congrArg (fun k : A ⨯ B ⟶ A' ↦ k.hom.app U (prodSection K A B x y))
      (prod.map_fst a b)
    change (prod.fst : A' ⨯ B' ⟶ A').hom.app U
        ((prod.map a b).hom.app U (prodSection K A B x y)) = _ at h
    rw [h, prodSection_fst]
    change a.hom.app U ((prod.fst : A ⨯ B ⟶ A).hom.app U
      (prodSection K A B x y)) = a.hom.app U x
    exact congrArg (fun z ↦ a.hom.app U z) (prodSection_fst K A B x y)
  · have h := congrArg (fun k : A ⨯ B ⟶ B' ↦ k.hom.app U (prodSection K A B x y))
      (prod.map_snd a b)
    change (prod.snd : A' ⨯ B' ⟶ B').hom.app U
        ((prod.map a b).hom.app U (prodSection K A B x y)) = _ at h
    rw [h, prodSection_snd]
    change b.hom.app U ((prod.snd : A ⨯ B ⟶ B).hom.app U
      (prodSection K A B x y)) = b.hom.app U y
    exact congrArg (fun z ↦ b.hom.app U z) (prodSection_snd K A B x y)

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_naturality (A B : Sheaf K (Type w)) {U V : Dᵒᵖ}
    (h : U ⟶ V) (a : A.obj.obj U) (b : B.obj.obj U) :
    (A ⨯ B).obj.map h (prodSection K A B a b) =
      prodSection K A B (A.obj.map h a) (B.obj.map h b) := by
  let a' : ((sheafToPresheaf K (Type w)).obj A).obj U := a
  let b' : ((sheafToPresheaf K (Type w)).obj B).obj U := b
  let e := PreservesLimitPair.iso (sheafToPresheaf K (Type w)) A B ≪≫
    FunctorToTypes.binaryProductIso
      ((sheafToPresheaf K (Type w)).obj A)
      ((sheafToPresheaf K (Type w)).obj B)
  have hn := congrArg (fun k ↦ k (a', b')) (e.inv.naturality h)
  change (A ⨯ B).obj.map h (e.inv.app U (a', b')) =
    e.inv.app V (A.obj.map h a', B.obj.map h b')
  exact hn.symm

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_lift {A B T : Sheaf K (Type w)}
    (a : T ⟶ A) (b : T ⟶ B) {U : Dᵒᵖ} (x : T.obj.obj U) :
    (prod.lift a b).hom.app U x =
      prodSection K A B (a.hom.app U x) (b.hom.app U x) := by
  apply prodSection_ext
  · have h := congrArg (fun k : T ⟶ A ↦ k.hom.app U x) (prod.lift_fst a b)
    exact h.trans (prodSection_fst K A B _ _).symm
  · have h := congrArg (fun k : T ⟶ B ↦ k.hom.app U x) (prod.lift_snd a b)
    exact h.trans (prodSection_snd K A B _ _).symm

omit [HasWeakSheafify K (Type w)] [HasWeakSheafify K GrpCat.{w}]
  [K.HasSheafCompose (CategoryTheory.forget GrpCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget GrpCat.{w})] in
private theorem prodSection_eta (A B : Sheaf K (Type w)) {U : Dᵒᵖ}
    (z : (A ⨯ B).obj.obj U) :
    prodSection K A B ((prod.fst : A ⨯ B ⟶ A).hom.app U z)
      ((prod.snd : A ⨯ B ⟶ B).hom.app U z) = z := by
  apply prodSection_ext
  · exact prodSection_fst K A B _ _
  · exact prodSection_snd K A B _ _

-- The torsor condition is the invertibility of (g, x) ↦ (g • x, x).
private theorem actionPair_isIso {G : Sheaf J GrpCat.{w}} (P : Torsor G) :
    IsIso (prod.lift (action P) (prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶
      P.carrier)) := by
  let A := (sheafForget J).obj G
  let t : A ⨯ P.carrier ⟶ P.carrier ⨯ P.carrier := prod.lift (action P) prod.snd
  have ht (U : Cᵒᵖ) : Function.Bijective (t.hom.app U) := by
    have hfst (z : (A ⨯ P.carrier).obj.obj U) :
        (prod.fst : P.carrier ⨯ P.carrier ⟶ P.carrier).hom.app U (t.hom.app U z) =
          (action P).hom.app U z :=
      congrArg (fun k : A ⨯ P.carrier ⟶ P.carrier ↦ k.hom.app U z)
        (prod.lift_fst (action P) prod.snd)
    have hsnd (z : (A ⨯ P.carrier).obj.obj U) :
        (prod.snd : P.carrier ⨯ P.carrier ⟶ P.carrier).hom.app U (t.hom.app U z) =
          (prod.snd : A ⨯ P.carrier ⟶ P.carrier).hom.app U z :=
      congrArg (fun k : A ⨯ P.carrier ⟶ P.carrier ↦ k.hom.app U z)
        (prod.lift_snd (action P) prod.snd)
    constructor
    · intro a b hab
      have hf := (hfst a).symm.trans
        ((congrArg (fun z ↦ (prod.fst : P.carrier ⨯ P.carrier ⟶
          P.carrier).hom.app U z) hab).trans (hfst b))
      have hs := (hsnd a).symm.trans
        ((congrArg (fun z ↦ (prod.snd : P.carrier ⨯ P.carrier ⟶
          P.carrier).hom.app U z) hab).trans (hsnd b))
      change (P.mulAction U.unop).smul
          ((prod.fst : A ⨯ P.carrier ⟶ A).hom.app U a)
          ((prod.snd : A ⨯ P.carrier ⟶ P.carrier).hom.app U a) =
        (P.mulAction U.unop).smul
          ((prod.fst : A ⨯ P.carrier ⟶ A).hom.app U b)
          ((prod.snd : A ⨯ P.carrier ⟶ P.carrier).hom.app U b) at hf
      apply prodSection_ext J
      · rw [hs] at hf
        exact (P.isCancelSMul U.unop).right_cancel' _ _ _ hf
      · exact hs
    · intro y
      obtain ⟨g, hg⟩ := (P.isPretransitive U.unop).exists_smul_eq
        ((prod.snd : P.carrier ⨯ P.carrier ⟶ P.carrier).hom.app U y)
        ((prod.fst : P.carrier ⨯ P.carrier ⟶ P.carrier).hom.app U y)
      let g' : A.obj.obj U := g
      let z := prodSection J (U := U) A P.carrier g'
        ((prod.snd : P.carrier ⨯ P.carrier ⟶ P.carrier).hom.app U y)
      refine ⟨z, ?_⟩
      apply prodSection_ext J
      · rw [hfst]
        change (P.mulAction U.unop).smul
          ((prod.fst : A ⨯ P.carrier ⟶ A).hom.app U z)
          ((prod.snd : A ⨯ P.carrier ⟶ P.carrier).hom.app U z) = _
        dsimp only [z]
        rw [prodSection_fst, prodSection_snd]
        exact hg
      · rw [hsnd]
        exact prodSection_snd J A P.carrier _ _
  haveI : IsIso ((sheafToPresheaf J (Type w)).map t) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun U ↦
      (CategoryTheory.isIso_iff_bijective _).2 (ht U)
  exact isIso_of_reflects_iso t (sheafToPresheaf J (Type w))

-- Exposing scalar multiplication requires access to its private product-section formula.
set_option backward.privateInPublic true in
/-- The sectionwise scalar multiplication transported by sheaf inverse image. -/
def pullbackSmul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D)
    (g : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U) :=
  (pullbackAction K f G P).hom.app (op U)
    (prodSection K
      ((sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G))
      ((f.sheafPullback (Type w) J K).obj P.carrier) g x)

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_actionPair_isIso (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    IsIso (prod.lift (pullbackAction K f G P)
      (prod.snd : (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G) ⨯
        (f.sheafPullback (Type w) J K).obj P.carrier ⟶
        (f.sheafPullback (Type w) J K).obj P.carrier)) := by
  let F := f.sheafPullback (Type w) J K
  let A := (sheafForget J).obj G
  let B := (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G)
  let c : B ≅ F.obj A :=
    (Functor.sheafPullback.compSheafComposeIso f
      (CategoryTheory.forget GrpCat.{w}) J K).app G
  let t : A ⨯ P.carrier ⟶ P.carrier ⨯ P.carrier := prod.lift (action P) prod.snd
  letI : IsIso t := actionPair_isIso P
  have he : prod.lift (pullbackAction K f G P)
        (prod.snd : B ⨯ F.obj P.carrier ⟶ F.obj P.carrier) =
      prod.map c.hom (𝟙 _) ≫ (PreservesLimitPair.iso F A P.carrier).inv ≫
        F.map t ≫ (PreservesLimitPair.iso F P.carrier P.carrier).hom := by
    apply prod.hom_ext
    · simp only [prod.lift_fst, Category.assoc, PreservesLimitPair.iso_hom]
      erw [prodComparison_fst, ← F.map_comp,
        show t ≫ prod.fst = action P from prod.lift_fst _ _]
      rfl
    · simp only [prod.lift_snd, Category.assoc, PreservesLimitPair.iso_hom]
      erw [prodComparison_snd, ← F.map_comp,
        show t ≫ prod.snd = (prod.snd : A ⨯ P.carrier ⟶ P.carrier) from
          prod.lift_snd _ _]
      rw [PreservesLimitPair.iso_inv_snd, prod.map_snd, Category.comp_id]
  rw [he]
  infer_instance

private theorem pullback_actionPair_bijective (G : Sheaf J GrpCat.{w}) (P : Torsor G)
    (U : Dᵒᵖ) : Function.Bijective
      ((prod.lift (pullbackAction K f G P)
        (prod.snd : (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G) ⨯
          (f.sheafPullback (Type w) J K).obj P.carrier ⟶
          (f.sheafPullback (Type w) J K).obj P.carrier)).hom.app U) := by
  letI := pullback_actionPair_isIso K f G P
  exact (CategoryTheory.isIso_iff_bijective _).1 inferInstance

/-- The unit of the inverse-image group acts trivially on the inverse-image carrier. -/
theorem pullback_one_smul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D)
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    pullbackSmul K f G P U 1 x = x := sorry

/-- The transported scalar multiplication respects multiplication of group sections. -/
theorem pullback_mul_smul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D)
    (g h : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    pullbackSmul K f G P U (g * h) x =
      pullbackSmul K f G P U g (pullbackSmul K f G P U h x) := sorry

/-- The explicit group action on the sections of the inverse-image carrier. -/
@[implicit_reducible]
def pullbackMulAction (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    MulAction (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
      (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) where
  smul := pullbackSmul K f G P U
  one_smul := pullback_one_smul K f G P U
  mul_smul := pullback_mul_smul K f G P U

/-- Restriction of inverse-image sections commutes with the transported action. -/
theorem pullback_act_naturality (G : Sheaf J GrpCat.{w}) (P : Torsor G)
    {U V : D} (h : V ⟶ U)
    (g : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : ((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U)) :
    ((f.sheafPullback (Type w) J K).obj P.carrier).obj.map h.op
        ((pullbackMulAction K f G P U).smul g x) =
      (pullbackMulAction K f G P V).smul
        (((f.sheafPullback GrpCat.{w} J K).obj G).obj.map h.op g)
        (((f.sheafPullback (Type w) J K).obj P.carrier).obj.map h.op x) := by
  let A : Sheaf K (Type w) :=
    (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G)
  let B : Sheaf K (Type w) := (f.sheafPullback (Type w) J K).obj P.carrier
  let g' : A.obj.obj (op U) := g
  let x' : B.obj.obj (op U) := x
  change B.obj.map h.op ((pullbackAction K f G P).hom.app (op U)
      (prodSection K (U := op U) A B g' x')) =
    (pullbackAction K f G P).hom.app (op V)
      (prodSection K (U := op V) A B (A.obj.map h.op g') (B.obj.map h.op x'))
  calc
    B.obj.map h.op ((pullbackAction K f G P).hom.app (op U)
        (prodSection K (U := op U) A B g' x')) =
      (ConcreteCategory.hom
        ((pullbackAction K f G P).hom.app (op U) ≫ B.obj.map h.op))
        (prodSection K (U := op U) A B g' x') := rfl
    _ = (ConcreteCategory.hom
        ((A ⨯ B).obj.map h.op ≫ (pullbackAction K f G P).hom.app (op V)))
        (prodSection K (U := op U) A B g' x') := by
      exact (ConcreteCategory.congr_hom
        ((pullbackAction K f G P).hom.naturality h.op)
        (prodSection K (U := op U) A B g' x')).symm
    _ = (pullbackAction K f G P).hom.app (op V)
        ((A ⨯ B).obj.map h.op
          (prodSection K (U := op U) A B g' x')) := rfl
    _ = (pullbackAction K f G P).hom.app (op V)
        (prodSection K (U := op V) A B (A.obj.map h.op g') (B.obj.map h.op x')) := by
      rw [prodSection_naturality]

/-- The transported action is pretransitive on sections over every object. -/
theorem pullback_isPretransitive (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    @MulAction.IsPretransitive
      (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
      (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U))
      (pullbackMulAction K f G P U).toSMul := by
  letI := pullbackMulAction K f G P U
  let A : Sheaf K (Type w) :=
    (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G)
  let B : Sheaf K (Type w) := (f.sheafPullback (Type w) J K).obj P.carrier
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨z, hz⟩ := (pullback_actionPair_bijective K f G P (op U)).2
    (prodSection K B B y x)
  have hf := congrArg (fun p ↦ (prod.fst : B ⨯ B ⟶ B).hom.app (op U) p) hz
  have hs := congrArg (fun p ↦ (prod.snd : B ⨯ B ⟶ B).hom.app (op U) p) hz
  erw [prodSection_lift, prodSection_fst, prodSection_fst] at hf
  erw [prodSection_lift, prodSection_snd, prodSection_snd] at hs
  refine ⟨(prod.fst : A ⨯ B ⟶ A).hom.app (op U) z, ?_⟩
  change (pullbackAction K f G P).hom.app (op U)
    (prodSection K A B ((prod.fst : A ⨯ B ⟶ A).hom.app (op U) z) x) = y
  rw [← hs, prodSection_eta]
  exact hf

/-- The transported action is free on sections over every object. -/
theorem pullback_isCancelSMul (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    @IsCancelSMul
      (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
      (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op U))
      (pullbackMulAction K f G P U).toSMul := by
  letI := pullbackMulAction K f G P U
  let A : Sheaf K (Type w) :=
    (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G)
  let B : Sheaf K (Type w) := (f.sheafPullback (Type w) J K).obj P.carrier
  refine { left_cancel' := (inferInstance : IsLeftCancelSMul
    (((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (B.obj.obj (op U))).left_cancel', right_cancel' := ?_ }
  intro g h x hgh
  let g' : A.obj.obj (op U) := g
  let h' : A.obj.obj (op U) := h
  have he := congrArg (fun y : B.obj.obj (op U) ↦ prodSection K B B y x) hgh
  have ht : (prod.lift (pullbackAction K f G P) (prod.snd : A ⨯ B ⟶ B)).hom.app
        (op U) (prodSection K A B g' x) =
      (prod.lift (pullbackAction K f G P) (prod.snd : A ⨯ B ⟶ B)).hom.app
        (op U) (prodSection K A B h' x) := by
    simp only [prodSection_lift, prodSection_snd]
    change prodSection K B B (pullbackSmul K f G P U g x) x =
      prodSection K B B (pullbackSmul K f G P U h x) x
    exact he
  have hi := (pullback_actionPair_bijective K f G P (op U)).1 ht
  have hf := congrArg (fun z ↦ (prod.fst : A ⨯ B ⟶ A).hom.app (op U) z) hi
  rw [prodSection_fst, prodSection_fst] at hf
  exact hf

include hLeftExact in
/-- The inverse image of the carrier of a torsor is locally nonempty. -/
theorem pullback_locallyNonempty (G : Sheaf J GrpCat.{w}) (P : Torsor G) (U : D) :
    ∃ S : Sieve U, S ∈ K U ∧
      ∀ ⦃V : D⦄ (h : V ⟶ U), S h →
        Nonempty (((f.sheafPullback (Type w) J K).obj P.carrier).obj.obj (op V)) := sorry

/-- Inverse image of a torsor under a continuous functor with left exact inverse image. -/
def pullback (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    Torsor ((f.sheafPullback GrpCat.{w} J K).obj G) where
  carrier := (f.sheafPullback (Type w) J K).obj P.carrier
  mulAction := pullbackMulAction K f G P
  act_naturality := pullback_act_naturality K f G P
  isPretransitive := pullback_isPretransitive K f G P
  isCancelSMul := pullback_isCancelSMul K f G P
  locallyNonempty := pullback_locallyNonempty K f G P

/-- The carrier of the inverse-image torsor is the inverse image of its carrier. -/
theorem pullback_carrier (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    (pullback K f G P).carrier = (f.sheafPullback (Type w) J K).obj P.carrier := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inverse image of an equivariant sheaf morphism is equivariant for the transported actions. -/
theorem pullback_map_comm {G : Sheaf J GrpCat.{w}} {P Q : Torsor G}
    (h : Torsor.Hom P Q) (U : D)
    (g : ((f.sheafPullback GrpCat.{w} J K).obj G).obj.obj (op U))
    (x : (pullback K f G P).Sections U) :
    ((f.sheafPullback (Type w) J K).map h.hom).hom.app (op U)
        (((pullback K f G P).mulAction U).smul g x) =
      ((pullback K f G Q).mulAction U).smul g
        (((f.sheafPullback (Type w) J K).map h.hom).hom.app (op U) x) := by
  let F := f.sheafPullback (Type w) J K
  let c : (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G) ⟶
      F.obj ((sheafForget J).obj G) := ((Functor.sheafPullback.compSheafComposeIso f
    (CategoryTheory.forget GrpCat.{w}) J K).app G).hom
  have ha : action P ≫ h.hom = prod.map (𝟙 _) h.hom ≫ action Q := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ConcreteCategory.hom_ext
    intro p
    have hf := congrArg (fun k : (sheafForget J).obj G ⨯ P.carrier ⟶
        (sheafForget J).obj G ↦ k.hom.app V p)
      (prod.map_fst (𝟙 ((sheafForget J).obj G)) h.hom)
    have hs := congrArg (fun k : (sheafForget J).obj G ⨯ P.carrier ⟶ Q.carrier ↦
        k.hom.app V p) (prod.map_snd (𝟙 ((sheafForget J).obj G)) h.hom)
    dsimp at hf hs
    change h.hom.hom.app V
        ((P.mulAction V.unop).smul
          ((prod.fst : (sheafForget J).obj G ⨯ P.carrier ⟶
            (sheafForget J).obj G).hom.app V p)
          ((prod.snd : (sheafForget J).obj G ⨯ P.carrier ⟶ P.carrier).hom.app V p)) =
      (Q.mulAction V.unop).smul
        ((prod.fst : (sheafForget J).obj G ⨯ Q.carrier ⟶
          (sheafForget J).obj G).hom.app V
          ((prod.map (𝟙 ((sheafForget J).obj G)) h.hom).hom.app V p))
        ((prod.snd : (sheafForget J).obj G ⨯ Q.carrier ⟶ Q.carrier).hom.app V
          ((prod.map (𝟙 ((sheafForget J).obj G)) h.hom).hom.app V p))
    rw [hf, hs]
    exact h.comm V.unop _ _
  have hn :
      (PreservesLimitPair.iso F ((sheafForget J).obj G) P.carrier).inv ≫
          F.map (prod.map (𝟙 ((sheafForget J).obj G)) h.hom) =
        prod.map (F.map (𝟙 ((sheafForget J).obj G))) (F.map h.hom) ≫
          (PreservesLimitPair.iso F ((sheafForget J).obj G) Q.carrier).inv := by
    apply (cancel_mono (PreservesLimitPair.iso F ((sheafForget J).obj G) Q.carrier).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [PreservesLimitPair.iso_hom, prodComparison_natural]
    rw [← PreservesLimitPair.iso_hom]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hc : pullbackAction K f G P ≫ F.map h.hom =
      prod.map (𝟙 _) (F.map h.hom) ≫ pullbackAction K f G Q := by
    change (prod.map c (𝟙 (F.obj P.carrier)) ≫
        (PreservesLimitPair.iso F ((sheafForget J).obj G) P.carrier).inv ≫
          F.map (action P)) ≫ F.map h.hom =
      prod.map (𝟙 _) (F.map h.hom) ≫
        prod.map c (𝟙 (F.obj Q.carrier)) ≫
          (PreservesLimitPair.iso F ((sheafForget J).obj G) Q.carrier).inv ≫
            F.map (action Q)
    rw [Category.assoc, Category.assoc, ← F.map_comp, ha, F.map_comp]
    rw [← Category.assoc _ _ (F.map (action Q)), hn]
    simp only [← Category.assoc, Functor.map_id, prod.map_map, Category.id_comp,
      Category.comp_id]
  let A : Sheaf K (Type w) :=
    (sheafForget K).obj ((f.sheafPullback GrpCat.{w} J K).obj G)
  let g' : A.obj.obj (op U) := g
  have he := congrArg (fun k ↦ k.hom.app (op U)
      (prodSection K (U := op U) A (F.obj P.carrier) g' x)) hc
  change (F.map h.hom).hom.app (op U)
      ((pullbackAction K f G P).hom.app (op U)
        (prodSection K (U := op U) A (F.obj P.carrier) g' x)) =
    (pullbackAction K f G Q).hom.app (op U)
      (prodSection K (U := op U) A (F.obj Q.carrier) g'
        ((F.map h.hom).hom.app (op U) x))
  change (F.map h.hom).hom.app (op U)
      ((pullbackAction K f G P).hom.app (op U)
        (prodSection K (U := op U) A (F.obj P.carrier) g' x)) =
    (pullbackAction K f G Q).hom.app (op U)
    ((prod.map (𝟙 A) (F.map h.hom)).hom.app (op U)
      (prodSection K (U := op U) A (F.obj P.carrier) g' x)) at he
  rw [he, prodSection_map]
  rfl

/-- Inverse image of an equivariant morphism of torsors. -/
def pullbackMap {G : Sheaf J GrpCat.{w}} {P Q : Torsor G} (h : Torsor.Hom P Q) :
    Torsor.Hom (pullback K f G P) (pullback K f G Q) where
  hom := (f.sheafPullback (Type w) J K).map h.hom
  comm := pullback_map_comm K f h

/-- Isomorphic torsors have equal inverse-image isomorphism classes. -/
theorem pullbackIsoClasses_sound (G : Sheaf J GrpCat.{w}) (P Q : Torsor G)
    (h : (Torsor.isomorphicSetoid G).r P Q) :
    (_root_.Quotient.mk'' (pullback K f G P) :
      Torsor.IsoClasses ((f.sheafPullback GrpCat.{w} J K).obj G)) =
      _root_.Quotient.mk'' (pullback K f G Q) := by
  letI : Category (Torsor G) := @Torsor.category C _ J G
  obtain ⟨e⟩ := h
  apply _root_.Quotient.sound
  let ehom : Torsor.Hom P Q :=
    @CategoryTheory.Iso.hom _ (@Torsor.category C _ J G) P Q e
  let einv : Torsor.Hom Q P :=
    @CategoryTheory.Iso.inv _ (@Torsor.category C _ J G) P Q e
  refine ⟨@CategoryTheory.Iso.mk _
    (@Torsor.category D _ K ((f.sheafPullback GrpCat.{w} J K).obj G))
    (pullback K f G P) (pullback K f G Q)
    (pullbackMap K f ehom) (pullbackMap K f einv) ?_ ?_⟩
  · apply PseudoTorsor.Hom.ext_hom
    change (f.sheafPullback (Type w) J K).map ehom.hom ≫
        (f.sheafPullback (Type w) J K).map einv.hom = 𝟙 _
    rw [← Functor.map_comp]
    rw [show ehom.hom ≫ einv.hom = 𝟙 _ by
      change (PseudoTorsor.comp e.hom e.inv).hom =
        (PseudoTorsor.id P.toPseudoTorsor).hom
      exact congrArg (fun k : Torsor.Hom P P ↦ k.hom)
        (@CategoryTheory.Iso.hom_inv_id _ (@Torsor.category C _ J G) P Q e)]
    simp
  · apply PseudoTorsor.Hom.ext_hom
    change (f.sheafPullback (Type w) J K).map einv.hom ≫
        (f.sheafPullback (Type w) J K).map ehom.hom = 𝟙 _
    rw [← Functor.map_comp]
    rw [show einv.hom ≫ ehom.hom = 𝟙 _ by
      change (PseudoTorsor.comp e.inv e.hom).hom =
        (PseudoTorsor.id Q.toPseudoTorsor).hom
      exact congrArg (fun k : Torsor.Hom Q Q ↦ k.hom)
        (@CategoryTheory.Iso.inv_hom_id _ (@Torsor.category C _ J G) P Q e)]
    simp

/-- The map on torsor isomorphism classes induced by sheaf inverse image. -/
def pullbackIsoClasses (G : Sheaf J GrpCat.{w}) :
    Torsor.IsoClasses G → Torsor.IsoClasses ((f.sheafPullback GrpCat.{w} J K).obj G) :=
  _root_.Quotient.lift (fun P ↦ _root_.Quotient.mk'' (pullback K f G P))
    (pullbackIsoClasses_sound K f G)

/-- The inverse-image map on isomorphism classes sends a representative to its inverse image. -/
theorem pullbackIsoClasses_mk (G : Sheaf J GrpCat.{w}) (P : Torsor G) :
    pullbackIsoClasses K f G (_root_.Quotient.mk'' P) = _root_.Quotient.mk'' (pullback K f G P) := rfl

end CategoryTheory.Sheaf.Torsor
