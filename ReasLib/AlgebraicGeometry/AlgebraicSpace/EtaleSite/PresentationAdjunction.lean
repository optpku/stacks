/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionComparison

/-!
# Étale restriction of type sheaves and geometric inverse image

Restriction has actual section maps for its unit and graph evaluation for its counit.
The full chart lift is used only for sheaves, with the genuine small-chart extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleTopos

variable {S : Scheme.{u}}

/-- The type-valued restriction diagram at an actual base-change object. -/
abbrev restrictTypeDiagram {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (F : Sheaf (smallEtaleTopology X) (Type u)) (V : smallEtaleSite X) :=
  StructuredArrow.proj (op ((etaleBaseChange p).obj V)) (smallEtaleToSpaces U).op ⋙
    (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)).obj F).obj

private theorem restrictTypeSquare_map {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (V : smallEtaleSite X)
    {a b : StructuredArrow (op ((etaleBaseChange p).obj V)) (smallEtaleToSpaces U).op}
    (g : a ⟶ b) :
    (restrictPostcompose p).map g.right.unop ≫
        restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a) =
      restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V b) := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  change (yoneda.obj V.left).map g.right.unop.left.op
      (yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSnd p V)) =
    yonedaEquiv (b.hom.unop.left ≫ etaleBaseChangeSnd p V)
  rw [yonedaEquiv_naturality, ← Category.assoc]
  have hw := congrArg (fun k ↦ k.unop.left) g.w
  change yoneda.map g.right.unop.left ≫ a.hom.unop.left = b.hom.unop.left at hw
  rw [hw]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit cone consists of the actual restriction maps of a type sheaf. -/
def restrictTypeUnitCone {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (F : Sheaf (smallEtaleTopology X) (Type u)) (V : smallEtaleSite X) :
    Cone (restrictTypeDiagram p F V) where
  pt := F.obj.obj (op V)
  π :=
    { app := fun a ↦ F.obj.map
        (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a)))
      naturality := by
        intro a b g
        change 𝟙 _ ≫ F.obj.map (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V b))) =
          F.obj.map (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a))) ≫
            F.obj.map (op ((restrictPostcompose p).map g.right.unop))
        simpa only [Category.id_comp, Functor.map_comp, op_comp] using!
          congrArg (fun k ↦ F.obj.map k.op) (restrictTypeSquare_map p V g).symm }

private theorem restrictTypeGraph_naturality {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    {V W : smallEtaleSite U} (h : V ⟶ W) :
    (smallEtaleToSpaces U).map h ≫ restrictGraphOver p W =
      restrictGraphOver p V ≫ (etaleBaseChange p).map ((restrictPostcompose p).map h) := by
  apply MorphismProperty.Over.Hom.ext
  change (yoneda.map h.left ≫
      pullback.lift (C := ((Over S)ᵒᵖ ⥤ Type u))
        (f := homFunctor p) (g := homFunctor ((restrictPostcompose p).obj W).hom)
        (homFunctor W.hom) (𝟙 _) rfl) =
    pullback.lift (C := ((Over S)ᵒᵖ ⥤ Type u))
      (f := homFunctor p) (g := homFunctor ((restrictPostcompose p).obj V).hom)
      (homFunctor V.hom) (𝟙 _) rfl ≫ etaleBaseChangeMapNat p ((restrictPostcompose p).map h)
  apply pullback.hom_ext (C := ((Over S)ᵒᵖ ⥤ Type u))
  · dsimp only [etaleBaseChangeMapNat, pullback.map]
    erw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst,
      Category.comp_id, pullback.lift_fst]
    exact smallEtaleSite.w h
  · dsimp only [etaleBaseChangeMapNat, pullback.map]
    erw [Category.assoc, pullback.lift_snd, Category.comp_id,
      Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      Category.id_comp]
    rfl

private theorem restrictTypeSquare_baseChange {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    {V W : smallEtaleSite X} (h : V ⟶ W)
    (a : StructuredArrow (op ((etaleBaseChange p).obj V)) (smallEtaleToSpaces U).op) :
    restrictPostcomposeHomOfSquare p
        (etaleSquareOfArrow p W
          (StructuredArrow.mk (((etaleBaseChange p).map h).op ≫ a.hom))) =
      restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a) ≫ h := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  change yonedaEquiv
      ((a.hom.unop.left ≫ etaleBaseChangeMapNat p h) ≫ etaleBaseChangeSndNat p W) =
    yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSndNat p V) ≫ h.left
  dsimp only [etaleBaseChangeMapNat, pullback.map, etaleBaseChangeSndNat]
  erw [Category.assoc, pullback.lift_snd, ← Category.assoc, yonedaEquiv_comp]
  rfl

private theorem restrictTypeSquare_graph {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (V : smallEtaleSite U) :
    restrictPostcomposeHomOfSquare p
        (etaleSquareOfArrow p ((restrictPostcompose p).obj V) (restrictGraphArrow p V)) =
      𝟙 ((restrictPostcompose p).obj V) := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  change yonedaEquiv
      (pullback.lift (C := ((Over S)ᵒᵖ ⥤ Type u))
        (f := homFunctor p) (g := homFunctor ((restrictPostcompose p).obj V).hom)
        (homFunctor V.hom) (𝟙 _) rfl ≫ pullback.snd _ _) = 𝟙 V.left
  rw [pullback.lift_snd]
  exact yonedaEquiv_yoneda_map (𝟙 V.left)

private theorem restrictTypeGraph_factorization {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (V : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange p).obj V)) (smallEtaleToSpaces U).op) :
    restrictGraphOver p a.right.unop ≫ (etaleBaseChange p).map
        (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a)) = a.hom.unop := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift (C := ((Over S)ᵒᵖ ⥤ Type u)) (f := homFunctor p)
      (g := homFunctor ((restrictPostcompose p).obj a.right.unop).hom)
      (homFunctor a.right.unop.hom) (𝟙 _) rfl ≫ etaleBaseChangeMapNat p
        (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a)) = a.hom.unop.left
  apply pullback.hom_ext (C := ((Over S)ᵒᵖ ⥤ Type u))
  · dsimp only [etaleBaseChangeMapNat, pullback.map]
    erw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
    have hw := a.hom.unop.w
    change a.hom.unop.left ≫ etaleBaseChangeFst p V = homFunctor a.right.unop.hom at hw
    exact hw.symm
  · dsimp only [etaleBaseChangeMapNat, pullback.map]
    erw [Category.assoc, pullback.lift_snd, ← Category.assoc,
      pullback.lift_snd, Category.id_comp]
    change yoneda.map (yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSndNat p V)) =
      a.hom.unop.left ≫ etaleBaseChangeSndNat p V
    apply yonedaEquiv.injective
    exact yonedaEquiv_yoneda_map _

private theorem restrictTypeEvaluation_precomp {U : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology U) (Type u))
    {W W' : spacesEtaleSite U} {V : smallEtaleSite U}
    (a : (smallEtaleToSpaces U).obj V ⟶ W') (k : W' ⟶ W) :
    ((extension U).obj F).obj.map k.op ≫ extensionEvaluation U F a =
      extensionEvaluation U F (a ≫ k) := by
  simp [extensionEvaluation, Category.assoc]

private theorem restrictTypeEvaluation_map {U : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology U) (Type u))
    {W : spacesEtaleSite U} {V V' : smallEtaleSite U}
    (a : (smallEtaleToSpaces U).obj V ⟶ W) (h : V' ⟶ V) :
    extensionEvaluation U F a ≫ F.obj.map h.op =
      extensionEvaluation U F ((smallEtaleToSpaces U).map h ≫ a) := by
  dsimp only [extensionEvaluation]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  exact congrArg (fun k ↦ ((extension U).obj F).obj.map a.op ≫ k)
    (((extensionRestrictionIso U).hom.app F).hom.naturality h.op).symm

private theorem restrictTypeEvaluation_ext {U : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology U) (Type u)) (W : spacesEtaleSite U)
    {A : Type u} {f g : A ⟶ ((extension U).obj F).obj.obj (op W)}
    (h : ∀ a : StructuredArrow (op W) (smallEtaleToSpaces U).op,
      f ≫ extensionEvaluation U F a.hom.unop = g ≫ extensionEvaluation U F a.hom.unop) :
    f = g :=
  (allChartIsLimit U F W).hom_ext h

private theorem restrictTypeUnitCone_lift_fac {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (F : Sheaf (smallEtaleTopology X) (Type u))
    (V : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange p).obj V)) (smallEtaleToSpaces U).op) :
    allChartLift U
        (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology U) (smallEtaleTopology X)).obj F)
        ((etaleBaseChange p).obj V) (restrictTypeUnitCone p F V) ≫
        extensionEvaluation U
          (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
            (smallEtaleTopology U) (smallEtaleTopology X)).obj F) a.hom.unop =
      F.obj.map (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a))) :=
  (allChartIsLimit U _ _).fac (restrictTypeUnitCone p F V) a

private theorem restrictTypeEvaluation_naturality {U : AlgebraicSpace S}
    (F G : Sheaf (smallEtaleTopology U) (Type u)) (f : F ⟶ G)
    {W : spacesEtaleSite U} {V : smallEtaleSite U}
    (a : (smallEtaleToSpaces U).obj V ⟶ W) :
    ((extension U).map f).hom.app (op W) ≫ extensionEvaluation U G a =
      extensionEvaluation U F a ≫ f.hom.app (op V) := by
  dsimp only [extensionEvaluation]
  rw [← Category.assoc, ← ((extension U).map f).hom.naturality, Category.assoc]
  exact congrArg (fun k ↦ ((extension U).obj F).obj.map a.op ≫ k)
    (congrArg (fun k ↦ k.hom.app (op V)) ((extensionRestrictionIso U).hom.naturality f))

private theorem restrictTypeUnitCone_lift_map {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (F : Sheaf (smallEtaleTopology X) (Type u))
    {V W : smallEtaleSite X} (h : V ⟶ W) :
    let Q := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)).obj F
    F.obj.map h.op ≫ allChartLift U Q _ (restrictTypeUnitCone p F V) =
      allChartLift U Q _ (restrictTypeUnitCone p F W) ≫
        ((extension U).obj Q).obj.map ((etaleBaseChange p).map h).op := by
  let Q := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology U) (smallEtaleTopology X)).obj F
  apply restrictTypeEvaluation_ext Q ((etaleBaseChange p).obj V)
  intro a
  let b : StructuredArrow (op ((etaleBaseChange p).obj W)) (smallEtaleToSpaces U).op :=
    StructuredArrow.mk (((etaleBaseChange p).map h).op ≫ a.hom)
  have hV := restrictTypeUnitCone_lift_fac p F V a
  have hW := restrictTypeUnitCone_lift_fac p F W b
  have hpre := restrictTypeEvaluation_precomp Q a.hom.unop ((etaleBaseChange p).map h)
  have hs : F.obj.map h.op ≫
      F.obj.map (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a))) =
      F.obj.map (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p W b))) := by
    exact (F.obj.map_comp h.op
      (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a)))).symm.trans
        (congrArg (fun k ↦ F.obj.map k.op) (restrictTypeSquare_baseChange p h a).symm)
  exact ((Category.assoc _ _ _).trans (congrArg (fun k ↦ F.obj.map h.op ≫ k) hV)).trans
    (hs.trans (hW.symm.trans ((congrArg
      (fun k ↦ allChartLift U Q _ (restrictTypeUnitCone p F W) ≫ k) hpre.symm).trans
        (Category.assoc _ _ _).symm)))

private theorem restrictTypeUnitCone_lift_naturality {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (F G : Sheaf (smallEtaleTopology X) (Type u))
    (f : F ⟶ G) (V : smallEtaleSite X) :
    let QF := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)).obj F
    let QG := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)).obj G
    f.hom.app (op V) ≫ allChartLift U QG _ (restrictTypeUnitCone p G V) =
      allChartLift U QF _ (restrictTypeUnitCone p F V) ≫
        ((extension U).map
          (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
            (smallEtaleTopology U) (smallEtaleTopology X)).map f)).hom.app
              (op ((etaleBaseChange p).obj V)) := by
  let QF := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology U) (smallEtaleTopology X)).obj F
  let QG := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology U) (smallEtaleTopology X)).obj G
  apply restrictTypeEvaluation_ext QG ((etaleBaseChange p).obj V)
  intro a
  have hF := restrictTypeUnitCone_lift_fac p F V a
  have hG := restrictTypeUnitCone_lift_fac p G V a
  have he := restrictTypeEvaluation_naturality QF QG
    (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)).map f) a.hom.unop
  have hn := (f.hom.naturality
    (op (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V a)))).symm
  exact ((Category.assoc _ _ _).trans (congrArg (fun k ↦ f.hom.app (op V) ≫ k) hG)).trans
    (hn.trans (((congrArg (fun k ↦ k ≫ f.hom.app
      (op ((restrictPostcompose p).obj a.right.unop))) hF.symm).trans
        (Category.assoc _ _ _)).trans ((congrArg
          (fun k ↦ allChartLift U QF _ (restrictTypeUnitCone p F V) ≫ k) he.symm).trans
            (Category.assoc _ _ _).symm)))

/-- The actual full-chart lift assembles the restriction maps into the unit. -/
def restrictTypeUnit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    𝟭 (Sheaf (smallEtaleTopology X) (Type u)) ⟶
      (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ⋙ typePushforward p where
  app F :=
    ⟨{ app := fun V ↦
        EtaleTopos.allChartLift U
          (((restrictPostcompose p).sheafPushforwardContinuous (Type u)
            (smallEtaleTopology U) (smallEtaleTopology X)).obj F)
          ((etaleBaseChange p).obj V.unop) (restrictTypeUnitCone p F V.unop)
       naturality := by
         intro V W h
         exact restrictTypeUnitCone_lift_map p F h.unop }⟩
  naturality := by
    intro F G f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact restrictTypeUnitCone_lift_naturality p F G f V.unop

/-- The counit evaluates the actual extended sheaf at the graph of its chart. -/
def restrictTypeCounit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    typePushforward p ⋙
      (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ⟶
      𝟭 (Sheaf (smallEtaleTopology U) (Type u)) where
  app F :=
    ⟨{ app := fun V ↦
        EtaleTopos.extensionEvaluation U F (restrictGraphOver p V.unop)
       naturality := by
         intro V W h
         change ((extension U).obj F).obj.map
             ((etaleBaseChange p).map ((restrictPostcompose p).map h.unop)).op ≫ _ = _
         calc
           _ = extensionEvaluation U F
               (restrictGraphOver p W.unop ≫
                 (etaleBaseChange p).map ((restrictPostcompose p).map h.unop)) :=
             restrictTypeEvaluation_precomp F _ _
           _ = extensionEvaluation U F
               ((smallEtaleToSpaces U).map h.unop ≫ restrictGraphOver p V.unop) :=
             congrArg (extensionEvaluation U F) (restrictTypeGraph_naturality p h.unop).symm
           _ = _ := (restrictTypeEvaluation_map F _ h.unop).symm }⟩
  naturality := by
    intro F G f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact restrictTypeEvaluation_naturality F G f (restrictGraphOver p V.unop)

/-- Étale restriction is adjoint to the genuine small-chart direct image. -/
def restrictTypeAdjunction {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ⊣ typePushforward p :=
  Adjunction.mkOfUnitCounit
    { unit := restrictTypeUnit p
      counit := restrictTypeCounit p
      left_triangle := by
        apply NatTrans.ext
        funext F
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        change allChartLift U _ _
            (restrictTypeUnitCone p F ((restrictPostcompose p).obj V.unop)) ≫
              extensionEvaluation U _ (restrictGraphOver p V.unop) = 𝟙 _
        have h := restrictTypeUnitCone_lift_fac p F ((restrictPostcompose p).obj V.unop)
          (restrictGraphArrow p V.unop)
        rw [restrictTypeSquare_graph] at h
        exact h.trans (F.obj.map_id _)
      right_triangle := by
        apply NatTrans.ext
        funext F
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        change allChartLift U _ _
            (restrictTypeUnitCone p ((typePushforward p).obj F) V.unop) ≫
              ((extension U).map ((restrictTypeCounit p).app F)).hom.app _ = 𝟙 _
        apply restrictTypeEvaluation_ext F ((etaleBaseChange p).obj V.unop)
        intro a
        let Q := ((restrictPostcompose p).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology U) (smallEtaleTopology X)).obj ((typePushforward p).obj F)
        let l := allChartLift U Q _
          (restrictTypeUnitCone p ((typePushforward p).obj F) V.unop)
        have he := restrictTypeEvaluation_naturality Q F ((restrictTypeCounit p).app F)
          a.hom.unop
        have hf := restrictTypeUnitCone_lift_fac p ((typePushforward p).obj F) V.unop a
        have hg := (restrictTypeEvaluation_precomp F (restrictGraphOver p a.right.unop)
          ((etaleBaseChange p).map
            (restrictPostcomposeHomOfSquare p (etaleSquareOfArrow p V.unop a)))).trans
              (congrArg (extensionEvaluation U F) (restrictTypeGraph_factorization p V.unop a))
        exact ((Category.assoc _ _ _).trans (congrArg (fun k ↦ l ≫ k) he)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k ↦ k ≫ ((restrictTypeCounit p).app F).hom.app a.right) hf).trans
              (hg.trans (Category.id_comp _).symm))) }

/-- The adjunction unit is the actual lift of the restriction-map cone. -/
@[simp]
theorem restrictTypeAdjunction_unit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictTypeAdjunction p).unit = restrictTypeUnit p := rfl

/-- The adjunction counit is the actual graph-evaluation map. -/
@[simp]
theorem restrictTypeAdjunction_counit {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictTypeAdjunction p).counit = restrictTypeCounit p := rfl

/-- Étale restriction is inverse image by uniqueness of these actual left adjoints. -/
def restrictTypeIsoInverseImage {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ≅
      (morphismOfTopoi p).inverseImage :=
  (restrictTypeAdjunction p).leftAdjointUniq (morphismOfTopoi p).adjunction

end AlgebraicGeometry.AlgebraicSpace.EtaleTopos
