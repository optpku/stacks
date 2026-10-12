/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
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
      homOfTopApp G H t U ≫ H.val.map i := sorry

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
    (homOfTop G H t).val.app (op ⊤) = t := sorry

/-- The reconstructed morphism has the unique zero component on the bottom open. -/
@[simp]
theorem homOfTop_app_bot [Nonempty X]
    (G H : SheafOfModules.{v} R)
    (t : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤)) :
    (homOfTop G H t).val.app (op (⊥ : Opens X)) = 0 := sorry

/-- Reconstructing a module-sheaf morphism from its component on the top open recovers the
original morphism. -/
@[simp]
theorem homOfTop_app_top_leftInverse
    (G H : SheafOfModules.{v} R) (f : G ⟶ H) :
    homOfTop G H (f.val.app (op (⊤ : Opens X))) = f := sorry

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
    homEquivTop G H f = f.val.app (op ⊤) := sorry

/-- Two morphisms of module sheaves on an indiscrete space agree if their top-open components
agree. -/
@[ext]
theorem hom_ext_top {G H : SheafOfModules.{v} R} {f g : G ⟶ H}
    (h : f.val.app (op (⊤ : Opens X)) = g.val.app (op ⊤)) : f = g := sorry

/-- Reconstructing the identity top-open component gives the identity module-sheaf morphism. -/
@[simp]
theorem homOfTop_id (G : SheafOfModules.{v} R) :
    homOfTop G G (𝟙 _) = 𝟙 G := sorry

/-- Reconstruction from the top open preserves composition. -/
@[simp]
theorem homOfTop_comp
    (G H K : SheafOfModules.{v} R)
    (f : G.val.obj (op (⊤ : Opens X)) ⟶ H.val.obj (op ⊤))
    (g : H.val.obj (op (⊤ : Opens X)) ⟶ K.val.obj (op ⊤)) :
    homOfTop G H f ≫ homOfTop H K g = homOfTop G K (f ≫ g) := sorry

/-- Top-open evaluation sends the identity module-sheaf morphism to the identity. -/
@[simp]
theorem homEquivTop_id (G : SheafOfModules.{v} R) :
    homEquivTop G G (𝟙 G) = 𝟙 _ := sorry

/-- Top-open evaluation preserves composition of module-sheaf morphisms. -/
@[simp]
theorem homEquivTop_comp
    {G H K : SheafOfModules.{v} R} (f : G ⟶ H) (g : H ⟶ K) :
    homEquivTop G K (f ≫ g) = homEquivTop G H f ≫ homEquivTop H K g := sorry

/-- The morphisms reconstructed from the two directions of a top-open isomorphism compose to the
identity on its source module sheaf. -/
theorem homOfTop_hom_inv_id
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    homOfTop G H e.hom ≫ homOfTop H G e.inv = 𝟙 G := sorry

/-- The morphisms reconstructed from the two directions of a top-open isomorphism compose to the
identity on its target module sheaf. -/
theorem homOfTop_inv_hom_id
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    homOfTop H G e.inv ≫ homOfTop G H e.hom = 𝟙 H := sorry

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
    (isoOfTop G H e).hom.val.app (op ⊤) = e.hom := sorry

/-- The top-open component of the inverse map of `isoOfTop` is the prescribed inverse map. -/
@[simp]
theorem isoOfTop_inv_app_top
    (G H : SheafOfModules.{v} R)
    (e : G.val.obj (op (⊤ : Opens X)) ≅ H.val.obj (op ⊤)) :
    (isoOfTop G H e).inv.val.app (op ⊤) = e.inv := sorry

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
    ofTopObj M (op (⊤ : Opens X)) = M := sorry

/-- The bottom-open value of `ofTopObj M` is the terminal module. -/
@[simp]
theorem ofTopObj_op_bot
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    ofTopObj M (op (⊥ : Opens X)) =
      ⊤_ ModuleCat.{v} (R.obj.obj (op (⊥ : Opens X))) := sorry

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
    ofTopMap M i = ofTopMapTop M i := sorry

/-- The restriction maps generated from a top-open module preserve identities. -/
theorem ofTopMap_id
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    (U : (Opens X)ᵒᵖ) :
    ofTopMap M (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (R.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (R.obj.map_id U))).inv.app (ofTopObj M U) := sorry

/-- The restriction maps generated from a top-open module preserve composition. -/
theorem ofTopMap_comp
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X))))
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    ofTopMap M (i ≫ j) =
      ofTopMap M i ≫
        (ModuleCat.restrictScalars (R.obj.map i).hom).map (ofTopMap M j) ≫
        (ModuleCat.restrictScalarsComp'
          (R.obj.map i).hom (R.obj.map j).hom (R.obj.map (i ≫ j)).hom
          (congrArg RingCat.Hom.hom (R.obj.map_comp i j))).inv.app (ofTopObj M W) := sorry

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
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (ofTopPresheaf M).presheaf := sorry

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
    (ofTop M).val = ofTopPresheaf M := sorry

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
      (topValueIso M).hom ≫ f := sorry

/-- Forming a morphism of generated sheaves preserves identities. -/
@[simp]
theorem ofTopHom_id
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    ofTopHom (𝟙 M) = 𝟙 (ofTop M) := sorry

/-- Forming a morphism of generated sheaves preserves composition. -/
@[simp]
theorem ofTopHom_comp
    {M N P : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))}
    (f : M ⟶ N) (g : N ⟶ P) :
    ofTopHom (f ≫ g) = ofTopHom f ≫ ofTopHom g := sorry

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
      (topValueIso M).hom ≫ f := sorry

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
      (unitIsoApp M).hom ≫ (topEvaluation R).map ((ofTopFunctor R).map f) := sorry

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
      (unitIsoApp M).inv ≫ f := sorry

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
    (unitNatTrans R).app M = (unitIsoApp M).hom := sorry

/-- A component of the inverse unit natural transformation is the inverse unit component. -/
@[simp, stacks 01BH "indiscrete equivalence inverse unit natural transformation component"]
theorem unitNatTransInv_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTransInv R).app M = (unitIsoApp M).inv := sorry

/-- The forward and inverse unit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit forward-inverse law"]
theorem unitNatTrans_hom_inv_id (R : TopCat.Sheaf RingCat.{u} X) :
    unitNatTrans R ≫ unitNatTransInv R = 𝟙 _ := sorry

/-- The inverse and forward unit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit inverse-forward law"]
theorem unitNatTrans_inv_hom_id (R : TopCat.Sheaf RingCat.{u} X) :
    unitNatTransInv R ≫ unitNatTrans R = 𝟙 _ := sorry

/-- The forward and inverse unit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit component forward-inverse law"]
theorem unitNatTrans_app_comp_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTrans R).app M ≫ (unitNatTransInv R).app M = 𝟙 _ := sorry

/-- The inverse and forward unit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence unit component inverse-forward law"]
theorem unitNatTransInv_app_comp_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitNatTransInv R).app M ≫ (unitNatTrans R).app M = 𝟙 _ := sorry

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
    (unitIso R).hom = unitNatTrans R := sorry

/-- The inverse natural transformation of `unitIso` is the named inverse unit transformation. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism inverse"]
theorem unitIso_inv (R : TopCat.Sheaf RingCat.{u} X) :
    (unitIso R).inv = unitNatTransInv R := sorry

/-- The component of `unitIso` is the canonical top-open unit isomorphism. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism component"]
theorem unitIso_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitIso R).app M = unitIsoApp M := sorry

/-- The forward component of `unitIso` is the named unit component. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism hom component"]
theorem unitIso_hom_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitIso R).hom.app M = (unitIsoApp M).hom := sorry

/-- The inverse component of `unitIso` is the named inverse unit component. -/
@[simp, stacks 01BH "indiscrete equivalence unit isomorphism inverse component"]
theorem unitIso_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (unitIso R).inv.app M = (unitIsoApp M).inv := sorry

/-- The component reconstructing a module sheaf from its value on the top open. -/
public noncomputable def counitIsoApp (G : SheafOfModules.{v} R) :
    (ofTopFunctor R).obj ((topEvaluation R).obj G) ≅ G :=
  isoOfTop _ G (topValueIso ((topEvaluation R).obj G))

/-- The reconstruction components for module sheaves are natural. -/
theorem counitIsoApp_naturality
    {G H : SheafOfModules.{v} R} (f : G ⟶ H) :
    (ofTopFunctor R).map ((topEvaluation R).map f) ≫ (counitIsoApp H).hom =
      (counitIsoApp G).hom ≫ f := sorry

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
      (counitIsoApp G).inv ≫ (ofTopFunctor R).map ((topEvaluation R).map f) := sorry

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
    (counitNatTrans R).app G = (counitIsoApp G).hom := sorry

/-- A component of the inverse counit natural transformation is the inverse counit component. -/
@[simp, stacks 01BH "indiscrete equivalence inverse counit natural transformation component"]
theorem counitNatTransInv_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTransInv R).app G = (counitIsoApp G).inv := sorry

/-- The forward and inverse counit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit forward-inverse law"]
theorem counitNatTrans_hom_inv_id (R : TopCat.Sheaf RingCat.{u} X) :
    counitNatTrans R ≫ counitNatTransInv R = 𝟙 _ := sorry

/-- The inverse and forward counit natural transformations compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit inverse-forward law"]
theorem counitNatTrans_inv_hom_id (R : TopCat.Sheaf RingCat.{u} X) :
    counitNatTransInv R ≫ counitNatTrans R = 𝟙 _ := sorry

/-- The forward and inverse counit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit component forward-inverse law"]
theorem counitNatTrans_app_comp_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTrans R).app G ≫ (counitNatTransInv R).app G = 𝟙 _ := sorry

/-- The inverse and forward counit components compose to the identity. -/
@[simp, stacks 01BH "indiscrete equivalence counit component inverse-forward law"]
theorem counitNatTransInv_app_comp_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitNatTransInv R).app G ≫ (counitNatTrans R).app G = 𝟙 _ := sorry

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
    (counitIso R).hom = counitNatTrans R := sorry

/-- The inverse natural transformation of `counitIso` is the named inverse counit transformation. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism inverse"]
theorem counitIso_inv (R : TopCat.Sheaf RingCat.{u} X) :
    (counitIso R).inv = counitNatTransInv R := sorry

/-- The component of `counitIso` is the canonical reconstruction isomorphism. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism component"]
theorem counitIso_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitIso R).app G = counitIsoApp G := sorry

/-- The forward component of `counitIso` is the named counit component. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism hom component"]
theorem counitIso_hom_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitIso R).hom.app G = (counitIsoApp G).hom := sorry

/-- The inverse component of `counitIso` is the named inverse counit component. -/
@[simp, stacks 01BH "indiscrete equivalence counit isomorphism inverse component"]
theorem counitIso_inv_app (R : TopCat.Sheaf RingCat.{u} X)
    (G : SheafOfModules.{v} R) :
    (counitIso R).inv.app G = (counitIsoApp G).inv := sorry

/-- The unit and counit for top-open generation satisfy the forward triangle identity. -/
theorem ofTop_triangle
    (M : ModuleCat.{v} (R.obj.obj (op (⊤ : Opens X)))) :
    (ofTopFunctor R).map ((unitIso R).hom.app M) ≫
      (counitIso R).hom.app ((ofTopFunctor R).obj M) =
        𝟙 ((ofTopFunctor R).obj M) := sorry

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
