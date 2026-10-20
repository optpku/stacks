module

public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Simplicial.SheafSystem
public import ReasLib.CategoryTheory.Sites.Simplicial.MorphismDiagram

/-!
# Sheaves on the total site of a morphism diagram

Comparison functors between `Sh(C_total)` and the category of sheaf systems attached to
the morphisms of topoi `f_φ` of a covariant simplex diagram of sites.
-/

-- The public isomorphisms use private component maps without adding public component API.
set_option backward.privateInPublic true

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

/-- Pushforwards of `toposMap C J` carry canonical identity and composition comparison isomorphisms. -/
instance instHasPushforwardFunctoriality_toposMap :
    HasPushforwardFunctoriality (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ toposMap.{u, v, w} C J φ) where
  pushforwardIdIso n := toposMap_pushforward_id C J n
  pushforwardCompIso ψ φ := toposMap_pushforward_comp.{u, v, w} C J ψ φ

/-- Restriction of a total sheaf to a stage satisfies the stage sheaf condition. -/
theorem restrictToDegree_isSheaf (n : SimplexCategory) (F : Sheaf (topology C J) (Type w)) :
    Presheaf.IsSheaf (J n).toGrothendieck ((ofStage C n).op ⋙ F.obj) := by
  sorry

/-- Restriction of a sheaf on `C_total` to the ordinary objects of the stage `C.obj n`. -/
def restrictToDegree (n : SimplexCategory) :
    Sheaf (topology C J) (Type w) ⥤ Sheaf (J n).toGrothendieck (Type w) where
  obj F := ⟨(ofStage C n).op ⋙ F.obj, restrictToDegree_isSheaf C J n F⟩
  map {F H} α := ObjectProperty.homMk
    { app := fun V ↦ α.hom.app ((ofStage C n).op.obj V), naturality := by intro X Y f; exact α.hom.naturality _ }
  map_id := by intro F; ext V x; rfl
  map_comp := by intro F H K α β; ext V x; rfl

/-- The underlying presheaf of `restrictToDegree n` is composition with `(ofStage n).op`. -/
theorem restrictToDegree_obj (n : SimplexCategory) (F : Sheaf (topology C J) (Type w)) :
    ((restrictToDegree C J n).obj F).obj = (ofStage C n).op ⋙ F.obj :=
  rfl

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

/-- Sectionwise transition maps commute with restrictions within a stage. -/
private theorem toSheafSystemMap_naturality (F : Sheaf (topology C J) (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : (C.obj m)ᵒᵖ} (η : V ⟶ W) :
    ((restrictToDegree C J m).obj F).obj.map η ≫ toSheafSystemMapApp C J F φ W =
      toSheafSystemMapApp C J F φ V ≫
        ((toposMap C J φ).pushforward.obj ((restrictToDegree C J n).obj F)).obj.map η := by
  sorry

/-- The transition of `toSheafSystem` at `φ` is restriction of `F` along `stageHom φ`. -/
def toSheafSystemMap (F : Sheaf (topology C J) (Type w)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictToDegree C J m).obj F ⟶
      (toposMap C J φ).pushforward.obj ((restrictToDegree C J n).obj F) :=
  ObjectProperty.homMk { app := toSheafSystemMapApp C J F φ, naturality := fun _ _ η ↦ toSheafSystemMap_naturality C J F φ η }

/-- Stage restrictions and transitions respect identities, composition, and sheaf morphisms. -/
private theorem toSheafSystem_laws :
    (∀ (F : Sheaf (topology C J) (Type w)) (n : SimplexCategory),
      toSheafSystemMap C J F (𝟙 n) = (toposMap_pushforward_id C J n).inv.app ((restrictToDegree C J n).obj F)) ∧
    (∀ (F : Sheaf (topology C J) (Type w)) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      toSheafSystemMap C J F (ψ ≫ φ) = toSheafSystemMap C J F ψ ≫
        (toposMap C J ψ).pushforward.map (toSheafSystemMap C J F φ) ≫
          (toposMap_pushforward_comp C J ψ φ).hom.app ((restrictToDegree C J n).obj F)) ∧
    (∀ {F H : Sheaf (topology C J) (Type w)} (α : F ⟶ H) {m n : SimplexCategory} (φ : m ⟶ n),
      toSheafSystemMap C J F φ ≫ (toposMap C J φ).pushforward.map ((restrictToDegree C J n).map α) =
        (restrictToDegree C J m).map α ≫ toSheafSystemMap C J H φ) := by
  sorry

/-- Extract the sheaf system of degreewise restrictions from a sheaf on `C_total`. -/
def toSheafSystem :
    Sheaf (topology C J) (Type w) ⥤
      SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ) where
  obj F :=
    SheafSystem.of (fun n ↦ (restrictToDegree C J n).obj F)
      (fun {m n} φ ↦ toSheafSystemMap C J F φ) ((toSheafSystem_laws C J).1 F) ((toSheafSystem_laws C J).2.1 F)
  map {F H} α :=
    SheafSystem.homMk (fun n ↦ (restrictToDegree C J n).map α) ((toSheafSystem_laws C J).2.2 α)
  map_id := by
    intro F
    apply SheafSystem.Hom.ext
    intro n
    exact (restrictToDegree C J n).map_id F
  map_comp := by
    intro F H K α β
    apply SheafSystem.Hom.ext
    intro n
    exact (restrictToDegree C J n).map_comp α β

/-- The stage sheaf of `toSheafSystem.obj F` at `n` is the restriction of `F` to `C.obj n`. -/
theorem toSheafSystem_obj_obj (F : Sheaf (topology C J) (Type w)) (n : SimplexCategory) :
    ((toSheafSystem C J).obj F).obj n = (restrictToDegree C J n).obj F :=
  rfl

/-- Restriction of a system along a total-category morphism `(φ, g) : U ⟶ V`. -/
def ofSheafSystemPresheafMap
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    {U V : totalSite C} (η : U ⟶ V) :
    (S.obj (degree V)).obj.obj (op V.unop.fiber.unop) ⟶ (S.obj (degree U)).obj.obj (op U.unop.fiber.unop) :=
  (S.map (homToPair η).1).hom.app (op V.unop.fiber.unop) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (C.map (homToPair η).1).toFunctor (Type w)
      (S.obj (degree U)) V.unop.fiber.unop).hom ≫
    (S.obj (degree U)).obj.map (homToPair η).2.op

/-- The assembled restriction maps preserve identities and composition. -/
private theorem ofSheafSystemPresheaf_laws (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) :
    (∀ W : (totalSite C)ᵒᵖ, ofSheafSystemPresheafMap C J S (𝟙 W).unop = 𝟙 _) ∧
    (∀ {W X Y : (totalSite C)ᵒᵖ} (η : W ⟶ X) (θ : X ⟶ Y),
      ofSheafSystemPresheafMap C J S (η ≫ θ).unop =
        ofSheafSystemPresheafMap C J S η.unop ≫ ofSheafSystemPresheafMap C J S θ.unop) := by
  sorry

/-- The assembled presheaf on `C_total` associated to a sheaf system: value at `U` is
`(S.obj (degree U))` at `obj U`, and restriction along `(φ, g)` is `F(φ)` then stage restriction. -/
def ofSheafSystemPresheaf
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) :
    (totalSite C)ᵒᵖ ⥤ Type w where
  obj W := (S.obj (degree W.unop)).obj.obj (op W.unop.unop.fiber.unop)
  map η := ofSheafSystemPresheafMap C J S η.unop
  map_id := (ofSheafSystemPresheaf_laws C J S).1
  map_comp := (ofSheafSystemPresheaf_laws C J S).2

/-- The component of a system morphism on sections over an object of `C_total`. -/
private def SheafSystem.Hom.appObj {S T : SheafSystem (fun n ↦ (J n).toGrothendieck)
    (fun φ ↦ toposMap C J φ)} (α : SheafSystem.Hom S T) (U : totalSite C) :
    (S.obj (degree U)).obj.obj (op U.unop.fiber.unop) ⟶ (T.obj (degree U)).obj.obj (op U.unop.fiber.unop) :=
  (α.app (degree U)).hom.app (op U.unop.fiber.unop)

/-- Assembly of a system of stage sheaves satisfies the total sheaf condition. -/
theorem ofSheafSystem_isSheaf (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) :
    Presheaf.IsSheaf (topology C J) (ofSheafSystemPresheaf C J S) := by
  sorry

/-- The section components of a system morphism commute with the assembled restrictions. -/
private theorem ofSheafSystemMap_naturality {S T : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)} (α : SheafSystem.Hom S T)
    {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    (ofSheafSystemPresheaf C J S).map η ≫ SheafSystem.Hom.appObj C J α Z.unop =
      SheafSystem.Hom.appObj C J α W.unop ≫ (ofSheafSystemPresheaf C J T).map η := by
  sorry

/-- Assemble a sheaf on `C_total` from a sheaf system. -/
def ofSheafSystem :
    SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ) ⥤
      Sheaf (topology C J) (Type w) where
  obj S := ⟨ofSheafSystemPresheaf C J S, ofSheafSystem_isSheaf C J S⟩
  map {S T} α := ObjectProperty.homMk
    { app := fun W ↦ SheafSystem.Hom.appObj C J α W.unop, naturality := fun _ _ η ↦ ofSheafSystemMap_naturality C J α η }
  map_id := by intro S; ext W x; rfl
  map_comp := by intro S T U α β; ext W x; rfl

/-- Sections of `ofSheafSystem.obj S` over `U` are the sections of `S.obj (degree U)` over
`obj U`. -/
theorem ofSheafSystem_obj_app
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    (U : totalSite C) :
    ((ofSheafSystem C J).obj S).obj.obj (op U) =
      (S.obj (degree U)).obj.obj (op U.unop.fiber.unop) :=
  rfl

/-- The identity on sections is natural from a total sheaf to its restriction and assembly. -/
private theorem unitIsoPresheaf_naturality (F : Sheaf (topology C J) (Type w))
    {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    F.obj.map η ≫ 𝟙 _ = 𝟙 _ ≫ (((ofSheafSystem C J).obj ((toSheafSystem C J).obj F)).obj).map η := by
  sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
private def unitIsoPresheaf (F : Sheaf (topology C J) (Type w)) :
    F.obj ⟶ ((ofSheafSystem C J).obj ((toSheafSystem C J).obj F)).obj where
  app := fun _ ↦ 𝟙 _
  naturality := fun _ _ η ↦ unitIsoPresheaf_naturality C J F η

/-- The identity on sections is natural from restriction and assembly back to a total sheaf. -/
private theorem unitIsoPresheafInv_naturality (F : Sheaf (topology C J) (Type w))
    {W Z : (totalSite C)ᵒᵖ} (η : W ⟶ Z) :
    (((ofSheafSystem C J).obj ((toSheafSystem C J).obj F)).obj).map η ≫ 𝟙 _ = 𝟙 _ ≫ F.obj.map η := by
  sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
private def unitIsoPresheafInv (F : Sheaf (topology C J) (Type w)) :
    ((ofSheafSystem C J).obj ((toSheafSystem C J).obj F)).obj ⟶ F.obj where
  app := fun _ ↦ 𝟙 _
  naturality := fun _ _ η ↦ unitIsoPresheafInv_naturality C J F η

/-- The sectionwise identity comparison commutes with morphisms of total sheaves. -/
private theorem unitIso_naturality {F H : Sheaf (topology C J) (Type w)} (α : F ⟶ H) :
    α ≫ ObjectProperty.homMk (unitIsoPresheaf C J H) =
      ObjectProperty.homMk (unitIsoPresheaf C J F) ≫
        (toSheafSystem C J ⋙ ofSheafSystem C J).map α := by
  sorry

/-- The unit isomorphism of the sheaf-system equivalence, with identity components on sections. -/
def unitIso :
    𝟭 (Sheaf (topology C J) (Type w)) ≅ toSheafSystem C J ⋙ ofSheafSystem C J :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ObjectProperty.homMk (unitIsoPresheaf C J F)
        inv := ObjectProperty.homMk (unitIsoPresheafInv C J F)
        hom_inv_id := by ext W x; rfl
        inv_hom_id := by ext W x; rfl })
    (fun α ↦ unitIso_naturality C J α)

/-- The identity on stage sections commutes with stage restrictions after assembly. -/
private theorem counitIsoHomApp_naturality (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) (n : SimplexCategory)
    {V W : (C.obj n)ᵒᵖ} (η : V ⟶ W) :
    (((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).obj n).obj.map η ≫ 𝟙 _ = 𝟙 _ ≫ (S.obj n).obj.map η := by
  sorry

/-- Stagewise sheaf morphism from the assembled-then-restricted system back to `S`. -/
private def counitIsoHomApp
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    (n : SimplexCategory) :
    ((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).obj n ⟶ S.obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := fun _ _ η ↦ counitIsoHomApp_naturality C J S n η }

/-- The identity on stage sections commutes with stage restrictions after assembly. -/
private theorem counitIsoInvApp_naturality (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) (n : SimplexCategory)
    {V W : (C.obj n)ᵒᵖ} (η : V ⟶ W) :
    (S.obj n).obj.map η ≫ 𝟙 _ = 𝟙 _ ≫ (((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).obj n).obj.map η := by
  sorry

/-- Stagewise sheaf morphism from `S` to the assembled-then-restricted system. -/
private def counitIsoInvApp
    (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ))
    (n : SimplexCategory) :
    S.obj n ⟶ ((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := fun _ _ η ↦ counitIsoInvApp_naturality C J S n η }

/-- The stagewise comparison with restriction of assembly respects transitions and morphisms. -/
private theorem counitIso_laws :
    (∀ (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) {m n : SimplexCategory} (φ : m ⟶ n),
      ((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).map φ ≫ (toposMap C J φ).pushforward.map (counitIsoHomApp C J S n) =
        counitIsoHomApp C J S m ≫ S.map φ) ∧
    (∀ (S : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) {m n : SimplexCategory} (φ : m ⟶ n),
      S.map φ ≫ (toposMap C J φ).pushforward.map (counitIsoInvApp C J S n) =
        counitIsoInvApp C J S m ≫ ((ofSheafSystem C J ⋙ toSheafSystem C J).obj S).map φ) ∧
    (∀ {S T : SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)} (α : SheafSystem.Hom S T) (n : SimplexCategory),
      ((ofSheafSystem C J ⋙ toSheafSystem C J).map α).app n ≫ counitIsoHomApp C J T n =
        counitIsoHomApp C J S n ≫ α.app n) := by
  sorry

/-- The counit isomorphism of the sheaf-system equivalence, with identity components on stages. -/
def counitIso :
    ofSheafSystem C J ⋙ toSheafSystem C J ≅
      𝟭 (SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ)) :=
  NatIso.ofComponents
    (fun S ↦
      { hom := SheafSystem.homMk (counitIsoHomApp C J S) ((counitIso_laws C J).1 S)
        inv := SheafSystem.homMk (counitIsoInvApp C J S) ((counitIso_laws C J).2.1 S)
        hom_inv_id := by
          apply SheafSystem.Hom.ext
          intro n
          ext V x
          rfl
        inv_hom_id := by
          apply SheafSystem.Hom.ext
          intro n
          ext V x
          rfl })
    (fun α ↦ SheafSystem.Hom.ext ((counitIso_laws C J).2.2 α))

/-- Sheaves on the total site are equivalent to systems of stage sheaves with compatible
pushforward transitions. -/
def sheafEquivalence :
    Sheaf (topology C J) (Type w) ≌
      SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ) :=
  Equivalence.mk (toSheafSystem C J) (ofSheafSystem C J) (unitIso C J) (counitIso C J)

/-- The forward functor of `sheafEquivalence C J` extracts the system of degreewise restrictions
and `f_φ`-maps. -/
theorem sheafEquivalence_functor :
    (sheafEquivalence C J).functor = toSheafSystem C J :=
  rfl

/-- The inverse functor of `sheafEquivalence C J` assembles a sheaf on `C_total` from a
system `(F_n, F(φ))`. -/
theorem sheafEquivalence_inverse :
    (sheafEquivalence C J).inverse = ofSheafSystem C J :=
  rfl

end CategoryTheory.SimplicialSites
