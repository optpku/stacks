module

public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Lemma_85_3_4_System
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

/-!
# Sheaves on the total site of a morphism diagram

Comparison functors between `Sh(C_total)` and the category of sheaf systems attached to
the morphisms of topoi `f_φ` of a covariant simplex diagram of sites.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
include h_morphism

/-- Direct images of `f_id` identify with the identity functor on `Sh(C n)` by continuous
pushforward along the identity law `C.map (𝟙 n) ≅ 𝟭`. -/
def toposMap_pushforward_id (n : SimplexCategory) :
    (toposMap.{u, v, w} C J (𝟙 n)).pushforward ≅ 𝟭 (Sheaf (J n).toGrothendieck (Type w)) :=
  Functor.sheafPushforwardContinuousId' (Cat.Hom.toNatIso (eqToIso (C.map_id n)))
    (Type w) (J n).toGrothendieck

/-- Pushforwards of `toposMap C J` are unital and strictly functorial in simplex operators. -/
instance instHasPushforwardFunctoriality_toposMap :
    HasPushforwardFunctoriality (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ toposMap.{u, v, w} C J φ) where
  pushforwardIdIso n := toposMap_pushforward_id C J n
  pushforwardCompIso ψ φ := toposMap_pushforward_comp.{u, v, w} C J ψ φ

/-- Restriction of a sheaf on `C_total` to the ordinary objects of the stage `C.obj n`. -/
def restrictToDegree (n : SimplexCategory) :
    Sheaf (topology C J) (Type w) ⥤ Sheaf (J n).toGrothendieck (Type w) where
  obj F := ⟨(ofStage C n).op ⋙ F.obj, sorry⟩
  map {F G} α := ObjectProperty.homMk
    { app := fun V ↦ α.hom.app ((ofStage C n).op.obj V), naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The underlying presheaf of `restrictToDegree n` is composition with `(ofStage n).op`. -/
theorem restrictToDegree_obj (n : SimplexCategory) (F : Sheaf (topology C J) (Type w)) :
    ((restrictToDegree C J n).obj F).obj = (ofStage C n).op ⋙ F.obj :=
  sorry

/-- The total-category arrow `(φ, 𝟙) : u_φ(V) ⟶ V` along which `F(φ)` is restriction. -/
def stageHom {m n : SimplexCategory} (φ : m ⟶ n) (V : C.obj m) :
    (ofStage C n).obj ((C.map φ).toFunctor.obj V) ⟶ (ofStage C m).obj V :=
  homMk φ (𝟙 ((C.map φ).toFunctor.obj V))

/-- Section component of `toSheafSystemMap` over an object of the source stage. -/
def toSheafSystemMapApp (F : Sheaf (topology C J) (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) (V : (C.obj m)ᵒᵖ) :
    ((restrictToDegree C J m).obj F).obj.obj V ⟶
      ((toposMap C J φ).pushforward.obj ((restrictToDegree C J n).obj F)).obj.obj V :=
  F.obj.map (stageHom C φ V.unop).op ≫
    (Functor.sheafPushforwardContinuousObjObjIso (C.map φ).toFunctor (Type w)
      ((restrictToDegree C J n).obj F) V.unop).inv

/-- The transition of `toSheafSystem` at `φ` is restriction of `F` along `stageHom φ`. -/
def toSheafSystemMap (F : Sheaf (topology C J) (Type w)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictToDegree C J m).obj F ⟶
      (toposMap C J φ).pushforward.obj ((restrictToDegree C J n).obj F) :=
  ObjectProperty.homMk { app := toSheafSystemMapApp C J F φ, naturality := sorry }

/-- Extract the sheaf system of degreewise restrictions from a sheaf on `C_total`. -/
def toSheafSystem :
    Sheaf (topology C J) (Type w) ⥤
      SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ) where
  obj F :=
    SheafSystem.of (fun n ↦ (restrictToDegree C J n).obj F)
      (fun {m n} φ ↦ toSheafSystemMap C J F φ) sorry sorry
  map {F G} α :=
    SheafSystem.homMk (fun n ↦ (restrictToDegree C J n).map α) sorry
  map_id := sorry
  map_comp := sorry

/-- The stage sheaf of `toSheafSystem.obj F` at `n` is the restriction of `F` to `C.obj n`. -/
theorem toSheafSystem_obj_obj (F : Sheaf (topology C J) (Type w)) (n : SimplexCategory) :
    ((toSheafSystem C J).obj F).obj n = (restrictToDegree C J n).obj F :=
  sorry

/-- Restriction of a system along a total-category morphism `(φ, g) : U ⟶ V`. -/
def ofSheafSystemPresheafMap
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    {U V : totalSite C} (η : U ⟶ V) :
    (S.obj (degree V)).obj.obj (op V.unop.fiber.unop) ⟶ (S.obj (degree U)).obj.obj (op U.unop.fiber.unop) :=
  (S.map (homToPair η).1).hom.app (op V.unop.fiber.unop) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (C.map (homToPair η).1).toFunctor (Type w)
      (S.obj (degree U)) V.unop.fiber.unop).hom ≫
    (S.obj (degree U)).obj.map (homToPair η).2.op

/-- The assembled presheaf on `C_total` associated to a sheaf system: value at `U` is
`(S.obj (degree U))` at `obj U`, and restriction along `(φ, g)` is `F(φ)` then stage restriction. -/
def ofSheafSystemPresheaf
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) :
    (totalSite C)ᵒᵖ ⥤ Type w where
  obj W := (S.obj (degree W.unop)).obj.obj (op W.unop.unop.fiber.unop)
  map {W Z} η := ofSheafSystemPresheafMap C J S η.unop
  map_id := sorry
  map_comp := sorry

/-- The component of a system morphism on sections over an object of `C_total`. -/
def SheafSystem.Hom.appObj {S T : SheafSystem (fun n ↦ (J n).toGrothendieck)
    (fun φ ↦ toposMap C J φ)} (α : SheafSystem.Hom S T) (U : totalSite C) :
    (S.obj (degree U)).obj.obj (op U.unop.fiber.unop) ⟶ (T.obj (degree U)).obj.obj (op U.unop.fiber.unop) :=
  (α.app (degree U)).hom.app (op U.unop.fiber.unop)

/-- Assemble a sheaf on `C_total` from a sheaf system. -/
def ofSheafSystem :
    SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ) ⥤
      Sheaf (topology C J) (Type w) where
  obj S := ⟨ofSheafSystemPresheaf C J S, sorry⟩
  map {S T} α := ObjectProperty.homMk
    { app := fun W ↦ SheafSystem.Hom.appObj C J α W.unop, naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Sections of `ofSheafSystem.obj S` over `U` are the sections of `S.obj (degree U)` over
`obj U`. -/
theorem ofSheafSystem_obj_app
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    (U : totalSite C) :
    ((ofSheafSystem C J).obj S).obj.obj (op U) =
      (S.obj (degree U)).obj.obj (op U.unop.fiber.unop) :=
  sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
def unitIsoPresheaf (F : Sheaf (topology C J) (Type w)) :
    F.obj ⟶ ((ofSheafSystem C J).obj ((toSheafSystem C J).obj F)).obj where
  app := fun _ ↦ 𝟙 _
  naturality := sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
def unitIsoPresheafInv (F : Sheaf (topology C J) (Type w)) :
    ((ofSheafSystem C J).obj ((toSheafSystem C J).obj F)).obj ⟶ F.obj where
  app := fun _ ↦ 𝟙 _
  naturality := sorry

/-- The unit isomorphism of the sheaf-system equivalence, with identity components on sections. -/
def unitIso :
    𝟭 (Sheaf (topology C J) (Type w)) ≅ toSheafSystem C J ⋙ ofSheafSystem C J :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ObjectProperty.homMk (unitIsoPresheaf C J F)
        inv := ObjectProperty.homMk (unitIsoPresheafInv C J F)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Stagewise sheaf morphism from the assembled-then-restricted system back to `S`. -/
def counitIsoHomApp
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    (n : SimplexCategory) :
    ((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).obj n ⟶ S.obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }

/-- Stagewise sheaf morphism from `S` to the assembled-then-restricted system. -/
def counitIsoInvApp
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    (n : SimplexCategory) :
    S.obj n ⟶ ((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }

/-- The counit isomorphism of the sheaf-system equivalence, with identity components on stages. -/
def counitIso :
    ofSheafSystem C J ⋙ toSheafSystem C J ≅
      𝟭 (SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) :=
  NatIso.ofComponents
    (fun S ↦
      { hom := SheafSystem.homMk (counitIsoHomApp C J S) sorry
        inv := SheafSystem.homMk (counitIsoInvApp C J S) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end CategoryTheory.SimplicialSites
