/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves on indiscrete spaces

For a sheaf of rings on an indiscrete space, a morphism of module sheaves is determined by its
component on the top open. This file exposes reconstruction, extensionality, and isomorphism APIs
at that natural level of generality. The one-point space `TopCat.of PUnit` is the main
specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u v w

namespace SheafOfModules.Indiscrete

variable {X : TopCat.{w}} [IndiscreteTopology X]
variable {R : TopCat.Sheaf RingCat.{u} X}

private theorem subsingleton_bot (G : SheafOfModules.{v} R) :
    Subsingleton (G.val.obj (op (⊥ : Opens X))) := by
  exact AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEmpty ((SheafOfModules.toSheaf R).obj G)).isZero

/-- The component on an open of a morphism between module sheaves on an indiscrete space,
reconstructed from its component on the top open. -/
public noncomputable def homOfTopApp
    (G H : SheafOfModules.{v} R)
    (t : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤))
    (U : (Opens X)ᵒᵖ) : G.val.obj U ⟶ H.val.obj U :=
  @dite (G.val.obj U ⟶ H.val.obj U)
    (U = op (⊤ : Opens X)) (Classical.propDecidable _)
    (fun hU ↦
      Eq.mp
        (congrArg (fun V ↦ G.val.obj V ⟶ H.val.obj V) hU).symm
        t)
    (fun _ ↦ 0)

/-- The components reconstructed from the top open satisfy the naturality equation for module
presheaf morphisms. -/
theorem homOfTopApp_naturality
    (G H : SheafOfModules.{v} R)
    (t : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    G.val.map i ≫
        (ModuleCat.restrictScalars (R.obj.map i).hom).map (homOfTopApp G H t V) =
      homOfTopApp G H t U ≫ H.val.map i := by
  classical
  by_cases hV : V = op (⊤ : Opens X)
  · subst V
    have hU : U = op (⊤ : Opens X) :=
      congrArg op (top_le_iff.mp i.unop.le)
    subst U
    have hi : i = 𝟙 (op (⊤ : Opens X)) := Subsingleton.elim _ _
    subst i
    simpa [homOfTopApp] using
      ((ModuleCat.restrictScalarsId'
        (R.obj.map (𝟙 (op (⊤ : Opens X)))).hom
        (congrArg RingCat.Hom.hom (R.obj.map_id (op ⊤)))).inv.naturality t).symm
  · have hVbot : V = op (⊥ : Opens X) :=
      congrArg op (V.unop.eq_bot_or_top.resolve_right (fun h ↦ hV (congrArg op h)))
    subst V
    letI : Subsingleton ((ModuleCat.restrictScalars (R.obj.map i).hom).obj
        (H.val.obj (op (⊥ : Opens X)))) :=
      ⟨fun x y ↦ (subsingleton_bot H).allEq x y⟩
    ext x
    exact Subsingleton.elim _ _

/-- A morphism between module sheaves on an indiscrete space, reconstructed explicitly from its
component on the top open. -/
public noncomputable def homOfTop
    (G H : SheafOfModules.{v} R)
    (t : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤)) : G ⟶ H :=
  ⟨
    { app := homOfTopApp G H t
      naturality := homOfTopApp_naturality G H t }
  ⟩

/-- The reconstructed morphism has the prescribed component on the top open. -/
@[simp]
theorem homOfTop_app_top
    (G H : SheafOfModules.{v} R)
    (t : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤)) :
    (homOfTop G H t).val.app (op ⊤) = t := by
  simp [homOfTop, homOfTopApp]

/-- The reconstructed morphism has the unique zero component on the bottom open. -/
@[simp]
theorem homOfTop_app_bot [Nonempty X]
    (G H : SheafOfModules.{v} R)
    (t : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤)) :
    (homOfTop G H t).val.app (op (⊥ : Opens X)) = 0 := by
  have h : op (⊥ : Opens X) ≠ op (⊤ : Opens X) :=
    fun h ↦ bot_ne_top (congrArg unop h)
  simp [homOfTop, homOfTopApp, h]

/-- Reconstructing a module-sheaf morphism from its component on the top open recovers the
original morphism. -/
@[simp]
theorem homOfTop_app_top_leftInverse
    (G H : SheafOfModules.{v} R) (f : G ⟶ H) :
    homOfTop G H (f.val.app (op (⊤ : Opens X))) = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  by_cases hU : U = op (⊤ : Opens X)
  · subst U
    exact homOfTop_app_top G H _
  · have hUbot : U = op (⊥ : Opens X) :=
      congrArg op (U.unop.eq_bot_or_top.resolve_right (fun h ↦ hU (congrArg op h)))
    subst U
    haveI := subsingleton_bot H
    ext x
    exact Subsingleton.elim _ _

/-- Morphisms between two module sheaves on an indiscrete space are determined exactly by their
component on the top open. -/
public noncomputable def homEquivTop (G H : SheafOfModules.{v} R) :
    (G ⟶ H) ≃ (G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤)) where
  toFun f := f.val.app (op ⊤)
  invFun := homOfTop G H
  left_inv := homOfTop_app_top_leftInverse G H
  right_inv := homOfTop_app_top G H

/-- Evaluating `homEquivTop` is literal evaluation on the top open. -/
@[simp]
theorem homEquivTop_apply (G H : SheafOfModules.{v} R) (f : G ⟶ H) :
    homEquivTop G H f = f.val.app (op ⊤) := rfl

/-- Two morphisms of module sheaves on an indiscrete space agree if their top-open components
agree. -/
@[ext]
theorem hom_ext_top {G H : SheafOfModules.{v} R} {f g : G ⟶ H}
    (h : f.val.app (op (⊤ : Opens X)) = g.val.app (op ⊤)) : f = g := by
  exact (homEquivTop G H).injective h

/-- Reconstructing the identity top-open component gives the identity module-sheaf morphism. -/
@[simp]
theorem homOfTop_id (G : SheafOfModules.{v} R) :
    homOfTop G G (𝟙 _) = 𝟙 G := by
  apply hom_ext_top
  simp

/-- Reconstruction from the top open preserves composition. -/
@[simp]
theorem homOfTop_comp
    (G H K : SheafOfModules.{v} R)
    (f : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤))
    (g : H.val.obj (op (⊤ : Opens X)) ⟶ K.val.obj (op ⊤)) :
    homOfTop G H f ≫ homOfTop H K g = homOfTop G K (f ≫ g) := by
  apply hom_ext_top
  simp

/-- Top-open evaluation sends the identity module-sheaf morphism to the identity. -/
@[simp]
theorem homEquivTop_id (G : SheafOfModules.{v} R) :
    homEquivTop G G (𝟙 G) = 𝟙 _ := rfl

/-- Top-open evaluation preserves composition of module-sheaf morphisms. -/
@[simp]
theorem homEquivTop_comp
    {G H K : SheafOfModules.{v} R} (f : G ⟶ H) (g : H ⟶ K) :
    homEquivTop G K (f ≫ g) = homEquivTop G H f ≫ homEquivTop H K g := rfl

/-- The morphisms reconstructed from the two directions of a top-open isomorphism compose to the
identity on its source module sheaf. -/
theorem homOfTop_hom_inv_id
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    homOfTop G H e.hom ≫ homOfTop H G e.inv = 𝟙 G := by
  rw [homOfTop_comp, e.hom_inv_id, homOfTop_id]

/-- The morphisms reconstructed from the two directions of a top-open isomorphism compose to the
identity on its target module sheaf. -/
theorem homOfTop_inv_hom_id
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    homOfTop H G e.inv ≫ homOfTop G H e.hom = 𝟙 H := by
  rw [homOfTop_comp, e.inv_hom_id, homOfTop_id]

/-- An isomorphism between the top-open values of two module sheaves on an indiscrete space
extends canonically to an isomorphism of module sheaves. -/
public noncomputable def isoOfTop
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) : G ≅ H where
  hom := homOfTop G H e.hom
  inv := homOfTop H G e.inv
  hom_inv_id := homOfTop_hom_inv_id G H e
  inv_hom_id := homOfTop_inv_hom_id G H e

/-- The top-open component of the forward map of `isoOfTop` is the prescribed forward map. -/
@[simp]
theorem isoOfTop_hom_app_top
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    (isoOfTop G H e).hom.val.app (op ⊤) = e.hom := by
  exact homOfTop_app_top G H e.hom

/-- The top-open component of the inverse map of `isoOfTop` is the prescribed inverse map. -/
@[simp]
theorem isoOfTop_inv_app_top
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    (isoOfTop G H e).inv.val.app (op ⊤) = e.inv := by
  exact homOfTop_app_top H G e.inv

section OfTop

variable [Nonempty X]

/-- The object part of the module presheaf generated by a module on the top open of an
indiscrete space. It has the given module at `⊤` and the terminal module elsewhere. -/
public noncomputable def ofTopObj
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    (U : (Opens X)ᵒᵖ) : ModuleCat.{v} (R.obj.obj U) :=
  @dite (ModuleCat.{v} (R.obj.obj U))
    (U = op (⊤ : Opens X)) (Classical.propDecidable _)
    (fun hU ↦
      Eq.mp (congrArg (fun V ↦ ModuleCat.{v} (R.obj.obj V)) hU).symm M)
    (fun _ ↦ ⊤_ ModuleCat.{v} (R.obj.obj U))

/-- The top-open value of `ofTopObj M` is the prescribed module `M`. -/
@[simp]
theorem ofTopObj_op_top
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    ofTopObj M (op (⊤ : Opens X)) = M := by
  simp [ofTopObj]

/-- The bottom-open value of `ofTopObj M` is the terminal module. -/
@[simp]
theorem ofTopObj_op_bot
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    ofTopObj M (op (⊥ : Opens X)) =
      ⊤_ ModuleCat.{v} (R.obj.obj (op (⊥ : Opens X))) := by
  have h : op (⊥ : Opens X) ≠ op (⊤ : Opens X) :=
    fun h ↦ bot_ne_top (congrArg unop h)
  simp [ofTopObj, h]

private theorem subsingleton_ofTopObj
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    {U : (Opens X)ᵒᵖ} (hU : U ≠ op (⊤ : Opens X)) :
    Subsingleton (ofTopObj M U) := by
  rw [ofTopObj, dif_neg hU]
  exact ModuleCat.subsingleton_of_isZero terminalIsTerminal.isZero

/-- The restriction map of `ofTopObj M` between two copies of the top open. -/
public noncomputable def ofTopMapTop
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    (i : op (⊤ : Opens X) ⟶ op ⊤) :
    ofTopObj M (op ⊤) ⟶
      (ModuleCat.restrictScalars (R.obj.map i).hom).obj (ofTopObj M (op ⊤)) :=
  @dite
    (ofTopObj M (op ⊤) ⟶
      (ModuleCat.restrictScalars (R.obj.map i).hom).obj (ofTopObj M (op ⊤)))
    (i = 𝟙 (op (⊤ : Opens X))) (Classical.propDecidable _)
    (fun hi ↦
      Eq.mp
        (congrArg
          (fun j : op (⊤ : Opens X) ⟶ op ⊤ ↦
            ofTopObj M (op ⊤) ⟶
              (ModuleCat.restrictScalars (R.obj.map j).hom).obj (ofTopObj M (op ⊤)))
          hi).symm
        ((ModuleCat.restrictScalarsId'
          (R.obj.map (𝟙 (op (⊤ : Opens X)))).hom
          (congrArg RingCat.Hom.hom (R.obj.map_id (op ⊤)))).inv.app
            (ofTopObj M (op ⊤))))
    (fun _ ↦ 0)

/-- The restriction map for the module presheaf generated by a module on the top open. -/
public noncomputable def ofTopMap
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ofTopObj M U ⟶
      (ModuleCat.restrictScalars (R.obj.map i).hom).obj (ofTopObj M V) :=
  @dite
    (ofTopObj M U ⟶
      (ModuleCat.restrictScalars (R.obj.map i).hom).obj (ofTopObj M V))
    (V = op (⊤ : Opens X)) (Classical.propDecidable _)
    (fun hV ↦
      @dite
        (ofTopObj M U ⟶
          (ModuleCat.restrictScalars (R.obj.map i).hom).obj (ofTopObj M V))
        (U = op (⊤ : Opens X)) (Classical.propDecidable _)
        (fun hU ↦
          match U, hU.symm, V, hV.symm with
          | _, rfl, _, rfl => ofTopMapTop M i)
        (fun _ ↦ 0))
    (fun _ ↦ 0)

/-- On the top open, `ofTopMap M` is the canonical top-to-top restriction map. -/
@[simp]
theorem ofTopMap_top
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    (i : op (⊤ : Opens X) ⟶ op ⊤) :
    ofTopMap M i = ofTopMapTop M i := by
  simp [ofTopMap]

/-- The restriction maps generated from a top-open module preserve identities. -/
theorem ofTopMap_id
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    (U : (Opens X)ᵒᵖ) :
    ofTopMap M (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (R.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (R.obj.map_id U))).inv.app (ofTopObj M U) := by
  classical
  by_cases hU : U = op (⊤ : Opens X)
  · subst U
    simp [ofTopMapTop]
  · haveI := subsingleton_ofTopObj M hU
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
    rfl

/-- The restriction maps generated from a top-open module preserve composition. -/
theorem ofTopMap_comp
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    ofTopMap M (i ≫ j) =
      ofTopMap M i ≫
        (ModuleCat.restrictScalars (R.obj.map i).hom).map (ofTopMap M j) ≫
        (ModuleCat.restrictScalarsComp'
          (R.obj.map i).hom (R.obj.map j).hom (R.obj.map (i ≫ j)).hom
          (congrArg RingCat.Hom.hom (R.obj.map_comp i j))).inv.app (ofTopObj M W) := by
  classical
  by_cases hW : W = op (⊤ : Opens X)
  · subst W
    have hV : V = op (⊤ : Opens X) :=
      congrArg op (top_le_iff.mp j.unop.le)
    subst V
    have hU : U = op (⊤ : Opens X) :=
      congrArg op (top_le_iff.mp i.unop.le)
    subst U
    have hi : i = 𝟙 (op (⊤ : Opens X)) := Subsingleton.elim _ _
    have hj : j = 𝟙 (op (⊤ : Opens X)) := Subsingleton.elim _ _
    subst i
    subst j
    ext x
    simp [ofTopMapTop]
  · haveI : Subsingleton (ofTopObj M W) := subsingleton_ofTopObj M hW
    letI : Subsingleton ((ModuleCat.restrictScalars (R.obj.map (i ≫ j)).hom).obj
        (ofTopObj M W)) :=
      ⟨fun x y ↦ (inferInstance : Subsingleton (ofTopObj M W)).allEq x y⟩
    ext x
    exact Subsingleton.elim _ _

/-- The presheaf of modules generated by a module on the top open of an indiscrete space. -/
public noncomputable def ofTopPresheaf
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    PresheafOfModules.{v} R.obj where
  obj := ofTopObj M
  map := ofTopMap M
  map_id := ofTopMap_id M
  map_comp := ofTopMap_comp M

/-- The presheaf generated by a module on the top open satisfies the sheaf condition. -/
theorem ofTopPresheaf_isSheaf
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (ofTopPresheaf M).presheaf := by
  haveI : Subsingleton (ofTopObj M (op (⊥ : Opens X))) := by
    rw [ofTopObj_op_bot]
    exact ModuleCat.subsingleton_of_isZero terminalIsTerminal.isZero
  letI : Subsingleton ((ofTopPresheaf M).presheaf.obj (op (⊥ : Opens X))) :=
    ⟨fun x y ↦ (inferInstance :
      Subsingleton (ofTopObj M (op (⊥ : Opens X)))).allEq x y⟩
  exact TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete
    (IndiscreteTopology.eq_top X) (ofTopPresheaf M).presheaf
    (AddCommGrpCat.isZero_of_subsingleton _).isTerminal

/-- The module sheaf generated by a module on the top open of a nonempty indiscrete space. -/
@[stacks 01BH "module sheaf generated from the top open of an indiscrete space"]
public noncomputable def ofTop
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) : SheafOfModules.{v} R where
  val := ofTopPresheaf M
  isSheaf := ofTopPresheaf_isSheaf M

/-- The underlying presheaf of `ofTop M` is the explicit presheaf generated from `M`. -/
@[simp]
theorem ofTop_val
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (ofTop M).val = ofTopPresheaf M := rfl

/-- The top-open value of `ofTop M` is canonically isomorphic to `M`. -/
public noncomputable def topValueIso
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    ofTopObj M (op (⊤ : Opens X)) ≅ M :=
  eqToIso (dif_pos rfl)

/-- A morphism between modules on the top open induces a morphism between their generated
module sheaves. -/
public noncomputable def ofTopHom
    {M N : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))} (f : M ⟶ N) :
    ofTop M ⟶ ofTop N :=
  homOfTop _ _ ((topValueIso M).hom ≫ f ≫ (topValueIso N).inv)

/-- The top-open component of `ofTopHom f` is the original morphism, through the canonical
top-value identifications. -/
@[simp]
theorem ofTopHom_app_top
    {M N : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))} (f : M ⟶ N) :
    (ofTopHom f).val.app (op (⊤ : Opens X)) ≫ (topValueIso N).hom =
      (topValueIso M).hom ≫ f := by
  simp [ofTopHom, Category.assoc]
  rfl

/-- Forming a morphism of generated sheaves preserves identities. -/
@[simp]
theorem ofTopHom_id
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    ofTopHom (𝟙 M) = 𝟙 (ofTop M) := by
  apply hom_ext_top
  simp [ofTopHom]

/-- Forming a morphism of generated sheaves preserves composition. -/
@[simp]
theorem ofTopHom_comp
    {M N P : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))}
    (f : M ⟶ N) (g : N ⟶ P) :
    ofTopHom (f ≫ g) = ofTopHom f ≫ ofTopHom g := by
  apply hom_ext_top
  simp [ofTopHom, Category.assoc]

/-- Modules over the ring on the top open determine module sheaves functorially. -/
@[stacks 01BH "modules as module sheaves on an indiscrete space"]
public noncomputable def ofTopFunctor (R : TopCat.Sheaf RingCat.{u} X) :
    ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))) ⥤ SheafOfModules.{v} R where
  obj M := ofTop M
  map f := ofTopHom f
  map_id := ofTopHom_id
  map_comp := ofTopHom_comp

/-- The action of `ofTopFunctor R` on morphisms is identified at the top open with the original
module morphism. -/
@[simp]
theorem ofTopFunctor_map_app_top
    {M N : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))} (f : M ⟶ N) :
    ((ofTopFunctor R).map f).val.app (op (⊤ : Opens X)) ≫ (topValueIso N).hom =
      (topValueIso M).hom ≫ f := by
  exact ofTopHom_app_top f

/-- Evaluation of a module sheaf on the top open of an indiscrete space. -/
public noncomputable abbrev topEvaluation (R : TopCat.Sheaf RingCat.{u} X) :
    SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))) :=
  SheafOfModules.evaluation R (op ⊤)

/-- The component identifying a top-open module with the top value of its generated sheaf. -/
public noncomputable def unitIsoApp
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    M ≅ (topEvaluation R).obj ((ofTopFunctor R).obj M) :=
  (topValueIso M).symm

/-- The unit components for top-open modules are natural. -/
theorem unitIsoApp_naturality
    {M N : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))} (f : M ⟶ N) :
    f ≫ (unitIsoApp N).hom =
      (unitIsoApp M).hom ≫ (topEvaluation R).map ((ofTopFunctor R).map f) := by
  change f ≫ (topValueIso N).inv =
    (topValueIso M).inv ≫ (ofTopHom f).val.app (op ⊤)
  apply (cancel_mono (topValueIso N).hom).1
  calc
    (f ≫ (topValueIso N).inv) ≫ (topValueIso N).hom = f := by simp
    _ = (topValueIso M).inv ≫ ((topValueIso M).hom ≫ f) := by simp
    _ = (topValueIso M).inv ≫
        ((ofTopHom f).val.app (op ⊤) ≫ (topValueIso N).hom) := by
      exact congrArg (fun k => (topValueIso M).inv ≫ k)
        (ofTopHom_app_top f).symm
    _ = ((topValueIso M).inv ≫ (ofTopHom f).val.app (op ⊤)) ≫
        (topValueIso N).hom := by simp [Category.assoc]

/-- The forward unit components form the natural transformation of the indiscrete equivalence. -/
@[stacks 01BH "indiscrete equivalence unit natural transformation"]
public noncomputable def unitNatTrans (R : TopCat.Sheaf RingCat.{u} X) :
    𝟭 (ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) ⟶
      ofTopFunctor R ⋙ topEvaluation R where
  app M := (unitIsoApp M).hom
  naturality _ _ f := unitIsoApp_naturality f

/-- The inverse unit components are natural in the top-open module. -/
@[stacks 01BH "indiscrete equivalence inverse unit naturality"]
theorem unitIsoApp_inv_naturality
    {M N : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))} (f : M ⟶ N) :
    (topEvaluation R).map ((ofTopFunctor R).map f) ≫ (unitIsoApp N).inv =
      (unitIsoApp M).inv ≫ f := by
  exact ofTopHom_app_top f

/-- The inverse unit components form the inverse natural transformation of the indiscrete
equivalence. -/
@[stacks 01BH "indiscrete equivalence inverse unit natural transformation"]
public noncomputable def unitNatTransInv (R : TopCat.Sheaf RingCat.{u} X) :
    ofTopFunctor R ⋙ topEvaluation R ⟶
      𝟭 (ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) where
  app M := (unitIsoApp M).inv
  naturality _ _ f := unitIsoApp_inv_naturality f

/-- A component of the forward unit natural transformation is the canonical unit component. -/
@[simp, stacks 01BH "indiscrete equivalence unit natural transformation component"]
theorem unitNatTrans_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTrans R).app M = (unitIsoApp M).hom := rfl

/-- A component of the inverse unit natural transformation is the inverse unit component. -/
@[simp, stacks 01BH "indiscrete equivalence inverse unit natural transformation component"]
theorem unitNatTransInv_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTransInv R).app M = (unitIsoApp M).inv := rfl

/-- The forward and inverse unit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit forward-inverse law"]
theorem unitNatTrans_hom_inv_id (R : TopCat.Sheaf RingCat.{u} X) :
    unitNatTrans R ≫ unitNatTransInv R = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  exact (unitIsoApp M).hom_inv_id

/-- The inverse and forward unit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit inverse-forward law"]
theorem unitNatTrans_inv_hom_id (R : TopCat.Sheaf RingCat.{u} X) :
    unitNatTransInv R ≫ unitNatTrans R = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  exact (unitIsoApp M).inv_hom_id

/-- The forward and inverse unit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit component forward-inverse law"]
theorem unitNatTrans_app_comp_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTrans R).app M ≫ (unitNatTransInv R).app M = 𝟙 _ := by
  exact (unitIsoApp M).hom_inv_id

/-- The inverse and forward unit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit component inverse-forward law"]
theorem unitNatTransInv_app_comp_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTransInv R).app M ≫ (unitNatTrans R).app M = 𝟙 _ := by
  exact (unitIsoApp M).inv_hom_id

/-- The identity on top-open modules is naturally isomorphic to generation followed by top-open
evaluation. -/
@[stacks 01BH "indiscrete equivalence unit isomorphism"]
public noncomputable def unitIso (R : TopCat.Sheaf RingCat.{u} X) :
    𝟭 (ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) ≅
      ofTopFunctor R ⋙ topEvaluation R :=
  { hom := unitNatTrans R
    inv := unitNatTransInv R
    hom_inv_id := unitNatTrans_hom_inv_id R
    inv_hom_id := unitNatTrans_inv_hom_id R }

/-- The forward natural transformation of `unitIso` is the named unit transformation. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism hom"]
theorem unitIso_hom (R : TopCat.Sheaf RingCat.{u} X) :
    (unitIso R).hom = unitNatTrans R := rfl

/-- The inverse natural transformation of `unitIso` is the named inverse unit transformation. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism inverse"]
theorem unitIso_inv (R : TopCat.Sheaf RingCat.{u} X) :
    (unitIso R).inv = unitNatTransInv R := rfl

/-- The component of `unitIso` is the canonical top-open unit isomorphism. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism component"]
theorem unitIso_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitIso R).app M = unitIsoApp M := by
  apply Iso.ext
  rfl

/-- The forward component of `unitIso` is the named unit component. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism hom component"]
theorem unitIso_hom_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitIso R).hom.app M = (unitIsoApp M).hom := rfl

/-- The inverse component of `unitIso` is the named inverse unit component. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism inverse component"]
theorem unitIso_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitIso R).inv.app M = (unitIsoApp M).inv := rfl

/-- The component reconstructing a module sheaf from its value on the top open. -/
public noncomputable def counitIsoApp (G : SheafOfModules.{v} R) :
    (ofTopFunctor R).obj ((topEvaluation R).obj G) ≅ G :=
  isoOfTop _ G (topValueIso ((topEvaluation R).obj G))

/-- The reconstruction components for module sheaves are natural. -/
theorem counitIsoApp_naturality
    {G H : SheafOfModules.{v} R} (f : G ⟶ H) :
    (ofTopFunctor R).map ((topEvaluation R).map f) ≫ (counitIsoApp H).hom =
      (counitIsoApp G).hom ≫ f := by
  apply hom_ext_top
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  change
    (ofTopHom (f.val.app (op ⊤))).val.app (op ⊤) ≫
        (counitIsoApp H).hom.val.app (op ⊤) =
      (counitIsoApp G).hom.val.app (op ⊤) ≫ f.val.app (op ⊤)
  have hH := isoOfTop_hom_app_top
    ((ofTopFunctor R).obj ((topEvaluation R).obj H)) H
      (topValueIso ((topEvaluation R).obj H))
  have hG := isoOfTop_hom_app_top
    ((ofTopFunctor R).obj ((topEvaluation R).obj G)) G
      (topValueIso ((topEvaluation R).obj G))
  rw [show (counitIsoApp H).hom.val.app (op ⊤) =
      (topValueIso ((topEvaluation R).obj H)).hom by simpa [counitIsoApp] using hH]
  rw [show (counitIsoApp G).hom.val.app (op ⊤) =
      (topValueIso ((topEvaluation R).obj G)).hom by simpa [counitIsoApp] using hG]
  exact ofTopHom_app_top (f.val.app (op ⊤))

/-- The forward counit components form the natural transformation of the indiscrete equivalence. -/
@[stacks 01BH "indiscrete equivalence counit natural transformation"]
public noncomputable def counitNatTrans (R : TopCat.Sheaf RingCat.{u} X) :
    topEvaluation R ⋙ ofTopFunctor R ⟶ 𝟭 (SheafOfModules.{v} R) where
  app G := (counitIsoApp G).hom
  naturality _ _ f := counitIsoApp_naturality f

/-- The inverse counit components are natural in the module sheaf. -/
@[stacks 01BH "indiscrete equivalence inverse counit naturality"]
theorem counitIsoApp_inv_naturality
    {G H : SheafOfModules.{v} R} (f : G ⟶ H) :
    f ≫ (counitIsoApp H).inv =
      (counitIsoApp G).inv ≫ (ofTopFunctor R).map ((topEvaluation R).map f) := by
  rw [← cancel_epi (counitIsoApp G).hom]
  simpa [Category.assoc] using
    congrArg (fun k ↦ k ≫ (counitIsoApp H).inv) (counitIsoApp_naturality f).symm

/-- The inverse counit components form the inverse natural transformation of the indiscrete
equivalence. -/
@[stacks 01BH "indiscrete equivalence inverse counit natural transformation"]
public noncomputable def counitNatTransInv (R : TopCat.Sheaf RingCat.{u} X) :
    𝟭 (SheafOfModules.{v} R) ⟶ topEvaluation R ⋙ ofTopFunctor R where
  app G := (counitIsoApp G).inv
  naturality _ _ f := counitIsoApp_inv_naturality f

/-- A component of the forward counit natural transformation is the canonical counit component. -/
@[simp, stacks 01BH "indiscrete equivalence counit natural transformation component"]
theorem counitNatTrans_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTrans R).app G = (counitIsoApp G).hom := rfl

/-- A component of the inverse counit natural transformation is the inverse counit component. -/
@[simp, stacks 01BH "indiscrete equivalence inverse counit natural transformation component"]
theorem counitNatTransInv_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTransInv R).app G = (counitIsoApp G).inv := rfl

/-- The forward and inverse counit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit forward-inverse law"]
theorem counitNatTrans_hom_inv_id (R : TopCat.Sheaf RingCat.{u} X) :
    counitNatTrans R ≫ counitNatTransInv R = 𝟙 _ := by
  apply NatTrans.ext
  funext G
  exact (counitIsoApp G).hom_inv_id

/-- The inverse and forward counit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit inverse-forward law"]
theorem counitNatTrans_inv_hom_id (R : TopCat.Sheaf RingCat.{u} X) :
    counitNatTransInv R ≫ counitNatTrans R = 𝟙 _ := by
  apply NatTrans.ext
  funext G
  exact (counitIsoApp G).inv_hom_id

/-- The forward and inverse counit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit component forward-inverse law"]
theorem counitNatTrans_app_comp_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTrans R).app G ≫ (counitNatTransInv R).app G = 𝟙 _ := by
  exact (counitIsoApp G).hom_inv_id

/-- The inverse and forward counit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit component inverse-forward law"]
theorem counitNatTransInv_app_comp_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTransInv R).app G ≫ (counitNatTrans R).app G = 𝟙 _ := by
  exact (counitIsoApp G).inv_hom_id

/-- Top-open evaluation followed by generation is naturally isomorphic to the identity on module
sheaves. -/
@[stacks 01BH "indiscrete equivalence counit isomorphism"]
public noncomputable def counitIso (R : TopCat.Sheaf RingCat.{u} X) :
    topEvaluation R ⋙ ofTopFunctor R ≅ 𝟭 (SheafOfModules.{v} R) :=
  { hom := counitNatTrans R
    inv := counitNatTransInv R
    hom_inv_id := counitNatTrans_hom_inv_id R
    inv_hom_id := counitNatTrans_inv_hom_id R }

/-- The forward natural transformation of `counitIso` is the named counit transformation. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism hom"]
theorem counitIso_hom (R : TopCat.Sheaf RingCat.{u} X) :
    (counitIso R).hom = counitNatTrans R := rfl

/-- The inverse natural transformation of `counitIso` is the named inverse counit transformation. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism inverse"]
theorem counitIso_inv (R : TopCat.Sheaf RingCat.{u} X) :
    (counitIso R).inv = counitNatTransInv R := rfl

/-- The component of `counitIso` is the canonical reconstruction isomorphism. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism component"]
theorem counitIso_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitIso R).app G = counitIsoApp G := by
  apply Iso.ext
  rfl

/-- The forward component of `counitIso` is the named counit component. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism hom component"]
theorem counitIso_hom_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitIso R).hom.app G = (counitIsoApp G).hom := rfl

/-- The inverse component of `counitIso` is the named inverse counit component. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism inverse component"]
theorem counitIso_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitIso R).inv.app G = (counitIsoApp G).inv := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit and counit for top-open generation satisfy the forward triangle identity. -/
theorem ofTop_triangle
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (ofTopFunctor R).map ((unitIso R).hom.app M) ≫
      (counitIso R).hom.app ((ofTopFunctor R).obj M) =
        𝟙 ((ofTopFunctor R).obj M) := by
  apply hom_ext_top
  simp [ofTopFunctor, ofTopHom, counitIsoApp, unitIsoApp]
  exact (topValueIso ((topEvaluation R).obj ((ofTopFunctor R).obj M))).inv_hom_id

/-- Modules over the top-open ring are canonically equivalent to module sheaves on a nonempty
indiscrete space. -/
@[stacks 01BH "module sheaves on an indiscrete space are modules on the top open"]
public noncomputable def equivalence (R : TopCat.Sheaf RingCat.{u} X) :
    ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))) ≌ SheafOfModules.{v} R where
  functor := ofTopFunctor R
  inverse := topEvaluation R
  unitIso := unitIso R
  counitIso := counitIso R
  functor_unitIso_comp := ofTop_triangle

/-- Generating module sheaves from modules on the top open is an equivalence of categories. -/
noncomputable instance ofTopFunctor_isEquivalence
    (R : TopCat.Sheaf RingCat.{u} X) : (ofTopFunctor R).IsEquivalence :=
  (equivalence R).isEquivalence_functor

end OfTop

end SheafOfModules.Indiscrete
