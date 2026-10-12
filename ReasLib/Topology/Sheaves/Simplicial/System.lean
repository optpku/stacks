/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Sheaves.InverseLimit.Category
public import ReasLib.Topology.Sheaves.Simplicial.Site

/-!
# Sheaf systems on a simplicial space

The category of systems of sheaves on the stages of a simplicial space and its equivalence with
sheaves on the associated simplicial Zariski site.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf.InverseLimit
open TopCat.Presheaf.Pushforward renaming id → pushforwardId
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u}) (C : Type (u + 1)) [Category.{u} C]

/-- The assembled presheaf on `X_Zar` associated to a sheaf system. -/
def ofSheafSystemPresheaf (S : SheafSystem (C := C) X) : (zariskiSite X)ᵒᵖ ⥤ C where
  obj W := (S.stageSheaf (op W.unop.simplex)).presheaf.obj (op W.unop.opens)
  map {W Z} η :=
    TopCat.Presheaf.PushforwardHomFamily.ofHomApp (S.stageMap η.unop.simplex.op).hom
      Z.unop.opens W.unop.opens η.unop.opens_le
  map_id := sorry
  map_comp := sorry

/-- The component of a system morphism on sections over an object of `ZariskiSite X`. -/
def _root_.TopCat.Sheaf.InverseLimit.SheafSystem.Hom.appOpens
    {S T : SheafSystem (C := C) X} (α : SheafSystem.Hom S T) (U : ZariskiSite X) :
    (S.stageSheaf (op U.simplex)).presheaf.obj (op U.opens) ⟶
      (T.stageSheaf (op U.simplex)).presheaf.obj (op U.opens) :=
  (α.app (op U.simplex)).hom.app (op U.opens)

/-- Assemble a sheaf on `X_Zar` from a sheaf system. -/
def ofSheafSystem : SheafSystem.asCategory (C := C) (F := X) ⥤ Sheaf (zariskiTopology X) C where
  obj S := ⟨ofSheafSystemPresheaf X C S, sorry⟩
  map {S T} α := ObjectProperty.homMk
    { app := fun W ↦ TopCat.Sheaf.InverseLimit.SheafSystem.Hom.appOpens X C α W.unop
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Sections of `ofSheafSystem.obj S` over `U` are the sections of `S.stageSheaf (op U.simplex)`
over `U.opens`. -/
theorem ofSheafSystem_obj_app (S : SheafSystem (C := C) X) (U : ZariskiSite X) :
    ((ofSheafSystem (C := C) X).obj S).obj.obj (op U) =
      (S.stageSheaf (op U.simplex)).presheaf.obj (op U.opens) := sorry

/-- Section component of `toSheafSystemMap` over an open of the target stage. -/
def toSheafSystemMapApp (F : Sheaf (zariskiTopology X) C) {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (V : (Opens (X.obj m))ᵒᵖ) :
    ((restrictToDegree X C m.unop).obj F).presheaf.obj V ⟶
      ((TopCat.Sheaf.pushforward C (X.map f)).obj
        ((restrictToDegree X C n.unop).obj F)).presheaf.obj V :=
  F.obj.map (pullbackHom X f V.unop).op

/-- The transition of `toSheafSystem` at `f : n ⟶ m` is restriction of `F` along `pullbackHom f`. -/
def toSheafSystemMap (F : Sheaf (zariskiTopology X) C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (restrictToDegree X C m.unop).obj F ⟶
      (TopCat.Sheaf.pushforward C (X.map f)).obj ((restrictToDegree X C n.unop).obj F) :=
  ⟨{ app := toSheafSystemMapApp X C F f, naturality := sorry }⟩


/-- Extract the sheaf system of degreewise restrictions from a sheaf on `X_Zar`. -/
def toSheafSystem : Sheaf (zariskiTopology X) C ⥤ SheafSystem.asCategory (C := C) (F := X) where
  obj F :=
    SheafSystem.of (F := X) (C := C)
      (fun n ↦ (restrictToDegree X C n.unop).obj F)
      (fun {n m} f ↦ toSheafSystemMap X C F f) sorry sorry
  map {F G} α :=
    TopCat.Sheaf.InverseLimit.SheafSystem.homMk
      (fun n ↦ (restrictToDegree X C n.unop).map α) sorry
  map_id := sorry
  map_comp := sorry

/-- The stage sheaf of `toSheafSystem.obj F` at `n` is the restriction of `F` to `X.obj n`. -/
theorem toSheafSystem_obj_obj (F : Sheaf (zariskiTopology X) C) (n : SimplexCategoryᵒᵖ) :
    ((toSheafSystem (C := C) X).obj F).stageSheaf n = (restrictToDegree X C n.unop).obj F := sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
def unitIsoPresheaf (F : Sheaf (zariskiTopology X) C) :
    F.obj ⟶ ((ofSheafSystem (C := C) X).obj ((toSheafSystem (C := C) X).obj F)).obj where
  app := fun W ↦ 𝟙 _
  naturality := sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
def unitIsoPresheafInv (F : Sheaf (zariskiTopology X) C) :
    ((ofSheafSystem (C := C) X).obj ((toSheafSystem (C := C) X).obj F)).obj ⟶ F.obj where
  app := fun W ↦ 𝟙 _
  naturality := sorry

/-- The unit isomorphism of the sheaf-system equivalence, with identity components on sections. -/
def unitIso : 𝟭 (Sheaf (zariskiTopology X) C) ≅ toSheafSystem (C := C) X ⋙ ofSheafSystem (C := C) X :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ObjectProperty.homMk (unitIsoPresheaf X C F)
        inv := ObjectProperty.homMk (unitIsoPresheafInv X C F)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Stagewise sheaf morphism from the assembled-then-restricted system back to `S`. -/
def counitIsoHomApp (S : SheafSystem (C := C) X) (n : SimplexCategoryᵒᵖ) :
    ((ofSheafSystem (C := C) X ⋙ toSheafSystem (C := C) X).obj S).stageSheaf n ⟶ S.stageSheaf n :=
  ⟨{ app := fun _ ↦ 𝟙 _, naturality := sorry }⟩

/-- Stagewise sheaf morphism from `S` to the assembled-then-restricted system. -/
def counitIsoInvApp (S : SheafSystem (C := C) X) (n : SimplexCategoryᵒᵖ) :
    S.stageSheaf n ⟶ ((ofSheafSystem (C := C) X ⋙ toSheafSystem (C := C) X).obj S).stageSheaf n :=
  ⟨{ app := fun _ ↦ 𝟙 _, naturality := sorry }⟩

/-- The counit isomorphism of the sheaf-system equivalence, with identity components on stages. -/
def counitIso : ofSheafSystem (C := C) X ⋙ toSheafSystem (C := C) X ≅
    𝟭 (SheafSystem.asCategory (C := C) (F := X)) :=
  NatIso.ofComponents
    (fun S ↦
      { hom := TopCat.Sheaf.InverseLimit.SheafSystem.homMk (counitIsoHomApp X C S) sorry
        inv := TopCat.Sheaf.InverseLimit.SheafSystem.homMk (counitIsoInvApp X C S) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The `C`-valued equivalence between sheaves on `X_Zar` and sheaf systems on `X`. -/
def sheafEquivalence : Sheaf (zariskiTopology X) C ≌
    SheafSystem.asCategory (C := C) (F := X) :=
  Equivalence.mk (toSheafSystem (C := C) X) (ofSheafSystem (C := C) X) (unitIso X C) (counitIso X C)

end CategoryTheory.SimplicialObject
