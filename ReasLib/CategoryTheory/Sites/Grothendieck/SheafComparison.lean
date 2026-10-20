/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Adjunction.KanExtension
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Simplicial.SheafSystem
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

/-!
# Sheaves on the total site of a fiberwise simplicial site

Comparison functors between `Sh(Grothendieck F)` and the category of sheaf systems attached
to the morphisms of topoi `f_φ` of a cocontinuous simplex diagram of sites.
-/

-- The public isomorphisms use private component maps without adding public component API.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [h_fiberwise : IsFiberwiseSite F J]
include h_fiberwise

/-- The inverse sheafification comparisons are natural in a stage sheaf. -/
private theorem toposMap_inverseImage_id_naturality (n : SimplexCategory)
    {P Q : Sheaf (J (op n)).toGrothendieck (Type w)} (α : P ⟶ Q) :
    (sheafToPresheaf (J (op n)).toGrothendieck (Type w) ⋙ presheafToSheaf (J (op n)).toGrothendieck (Type w)).map α ≫
        (sheafificationIso Q).inv = (sheafificationIso P).inv ≫ α := by
  sorry

/-- Inverse images of `f_id` identify with the identity functor on `Sh(C n)` by sheafified
precomposition along `F.map (𝟙 n).op ≅ 𝟭`. -/
def toposMap_inverseImage_id (n : SimplexCategory) :
    (toposMap F J (𝟙 n)).inverseImage ≅ 𝟭 (Sheaf (J (op n)).toGrothendieck (Type w)) :=
  let e := Cat.Hom.toNatIso (eqToIso (F.map_id (op n))) ≪≫ eqToIso Cat.Hom.id_toFunctor
  let Jt := (J (op n)).toGrothendieck
  Functor.isoWhiskerLeft (sheafToPresheaf Jt (Type w))
      (Functor.isoWhiskerRight ((Functor.whiskeringLeft _ _ (Type w)).mapIso (NatIso.op e).symm)
        (presheafToSheaf Jt (Type w))) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf Jt (Type w))
      (Functor.isoWhiskerRight (Functor.whiskeringLeftObjIdIso) (presheafToSheaf Jt (Type w))) ≪≫
    NatIso.ofComponents (fun P ↦ (sheafificationIso P).symm)
      (fun α ↦ toposMap_inverseImage_id_naturality F J n α)

/-- Direct images of `f_id` identify with the identity functor on `Sh(C n)` by uniqueness of
right adjoints along `toposMap_inverseImage_id`. -/
def toposMap_pushforward_id (n : SimplexCategory) :
    (toposMap F J (𝟙 n)).pushforward ≅ 𝟭 (Sheaf (J (op n)).toGrothendieck (Type w)) :=
  Adjunction.rightAdjointUniq
    ((toposMap F J (𝟙 n)).adjunction.ofNatIsoLeft (toposMap_inverseImage_id F J n))
    Adjunction.id

/-- Pushforwards of `toposMap F J` carry canonical identity and composition comparison isomorphisms. -/
instance instHasPushforwardFunctoriality_toposMap :
    SimplicialSites.HasPushforwardFunctoriality
      (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ) where
  pushforwardIdIso n := toposMap_pushforward_id F J n
  pushforwardCompIso ψ φ := toposMap_pushforward_comp F J ψ φ

/-- Restriction of a total sheaf to a stage satisfies the stage sheaf condition. -/
theorem restrictToDegree_isSheaf (n : SimplexCategory) (G : Sheaf (topology F J) (Type w)) :
    Presheaf.IsSheaf (J (op n)).toGrothendieck ((ι F (op n)).op ⋙ G.obj) := by
  sorry

/-- Restriction of a sheaf on the total site to the fiber `F.obj (op n)`. -/
def restrictToDegree (n : SimplexCategory) :
    Sheaf (topology F J) (Type w) ⥤ Sheaf (J (op n)).toGrothendieck (Type w) where
  obj G := ⟨(ι F (op n)).op ⋙ G.obj, restrictToDegree_isSheaf F J n G⟩
  map {G H} α := ObjectProperty.homMk
    { app := fun V ↦ α.hom.app ((ι F (op n)).op.obj V), naturality := by intro X Y f; exact α.hom.naturality _ }
  map_id := by intro G; ext V x; rfl
  map_comp := by intro G H K α β; ext V x; rfl

/-- The underlying presheaf of `restrictToDegree n` is composition with `(ι F (op n)).op`. -/
theorem restrictToDegree_obj (n : SimplexCategory) (G : Sheaf (topology F J) (Type w)) :
    ((restrictToDegree F J n).obj G).obj = (ι F (op n)).op ⋙ G.obj :=
  rfl

/-- The total-category arrow `(φ, 𝟙) : V ⟶ u_φ(V)` along which `F(φ)` is restriction. -/
def stageHom {m n : SimplexCategory} (φ : m ⟶ n) (V : F.obj (op n)) :
    (ι F (op n)).obj V ⟶ (ι F (op m)).obj ((F.map φ.op).toFunctor.obj V) :=
  Hom.mk φ.op (𝟙 ((F.map φ.op).toFunctor.obj V))

/-- Restriction along a simplex operator is natural in the object of its target stage. -/
private theorem toSheafSystemMapPresheaf_naturality (G : Sheaf (topology F J) (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : (F.obj (op n))ᵒᵖ} (η : V ⟶ W) :
    ((F.map φ.op).toFunctor.op ⋙ ((restrictToDegree F J m).obj G).obj).map η ≫
        G.obj.map (stageHom F φ W.unop).op =
      G.obj.map (stageHom F φ V.unop).op ≫ ((restrictToDegree F J n).obj G).obj.map η := by
  sorry

/-- Presheaf-level transition of `toSheafSystem` at `φ`, the Ran mate of restriction along
`stageHom φ`. -/
def toSheafSystemMapPresheaf (G : Sheaf (topology F J) (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((restrictToDegree F J m).obj G).obj ⟶
      ((toposMap F J φ).pushforward.obj ((restrictToDegree F J n).obj G)).obj :=
  ((F.map φ.op).toFunctor.op.ranAdjunction (Type w)).homEquiv
      ((restrictToDegree F J m).obj G).obj ((restrictToDegree F J n).obj G).obj
    { app := fun V ↦ G.obj.map (stageHom F φ V.unop).op, naturality := fun _ _ η ↦ toSheafSystemMapPresheaf_naturality F J G φ η }

/-- The transition of `toSheafSystem` at `φ` is the sheaf morphism associated to the Ran mate of
restriction along `stageHom φ`. -/
def toSheafSystemMap (G : Sheaf (topology F J) (Type w)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictToDegree F J m).obj G ⟶
      (toposMap F J φ).pushforward.obj ((restrictToDegree F J n).obj G) :=
  ObjectProperty.homMk (toSheafSystemMapPresheaf F J G φ)

/-- Stage restrictions and transitions respect identities, composition, and sheaf morphisms. -/
private theorem toSheafSystem_laws :
    (∀ (G : Sheaf (topology F J) (Type w)) (n : SimplexCategory),
      toSheafSystemMap F J G (𝟙 n) = (toposMap_pushforward_id F J n).inv.app ((restrictToDegree F J n).obj G)) ∧
    (∀ (G : Sheaf (topology F J) (Type w)) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      toSheafSystemMap F J G (ψ ≫ φ) = toSheafSystemMap F J G ψ ≫
        (toposMap F J ψ).pushforward.map (toSheafSystemMap F J G φ) ≫
          (toposMap_pushforward_comp F J ψ φ).hom.app ((restrictToDegree F J n).obj G)) ∧
    (∀ {G H : Sheaf (topology F J) (Type w)} (α : G ⟶ H) {m n : SimplexCategory} (φ : m ⟶ n),
      toSheafSystemMap F J G φ ≫ (toposMap F J φ).pushforward.map ((restrictToDegree F J n).map α) =
        (restrictToDegree F J m).map α ≫ toSheafSystemMap F J H φ) := by
  sorry

/-- Extract the sheaf system of degreewise restrictions from a sheaf on the total site. -/
def toSheafSystem :
    Sheaf (topology F J) (Type w) ⥤
      SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ toposMap F J φ) where
  obj G :=
    SimplicialSites.SheafSystem.of (fun n ↦ (restrictToDegree F J n).obj G)
      (fun {m n} φ ↦ toSheafSystemMap F J G φ) ((toSheafSystem_laws F J).1 G) ((toSheafSystem_laws F J).2.1 G)
  map {G H} α :=
    SimplicialSites.SheafSystem.homMk (fun n ↦ (restrictToDegree F J n).map α) ((toSheafSystem_laws F J).2.2 α)
  map_id := by
    intro G
    apply SimplicialSites.SheafSystem.Hom.ext
    intro n
    exact (restrictToDegree F J n).map_id G
  map_comp := by
    intro G H K α β
    apply SimplicialSites.SheafSystem.Hom.ext
    intro n
    exact (restrictToDegree F J n).map_comp α β

/-- The stage sheaf of `toSheafSystem.obj G` at `n` is the restriction of `G` to `F.obj (op n)`. -/
theorem toSheafSystem_obj_obj (G : Sheaf (topology F J) (Type w)) (n : SimplexCategory) :
    ((toSheafSystem F J).obj G).obj n = (restrictToDegree F J n).obj G :=
  rfl

/-- Restriction of a system along a morphism of the Grothendieck construction. -/
def ofSheafSystemPresheafMap
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    {X Y : Grothendieck F} (h : X ⟶ Y) :
    (S.obj Y.base.unop).obj.obj (op Y.fiber) ⟶ (S.obj X.base.unop).obj.obj (op X.fiber) :=
  (S.obj Y.base.unop).obj.map h.fiber.op ≫
    ((sheafificationAdjunction (J X.base).toGrothendieck (Type w)).unit.app
        ((F.map h.base).toFunctor.op ⋙ (S.obj Y.base.unop).obj)).app (op X.fiber) ≫
    (SimplicialSites.SheafSystem.mapInverseImage S h.base.unop).hom.app (op X.fiber)

/-- The assembled restriction maps preserve identities and composition. -/
private theorem ofSheafSystemPresheaf_laws (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)) :
    (∀ W : (Grothendieck F)ᵒᵖ, ofSheafSystemPresheafMap F J S (𝟙 W).unop = 𝟙 _) ∧
    (∀ {W X Y : (Grothendieck F)ᵒᵖ} (η : W ⟶ X) (θ : X ⟶ Y),
      ofSheafSystemPresheafMap F J S (η ≫ θ).unop =
        ofSheafSystemPresheafMap F J S η.unop ≫ ofSheafSystemPresheafMap F J S θ.unop) := by
  sorry

/-- The assembled presheaf on `Grothendieck F` associated to a sheaf system. -/
def ofSheafSystemPresheaf
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ)) :
    (Grothendieck F)ᵒᵖ ⥤ Type w where
  obj W := (S.obj W.unop.base.unop).obj.obj (op W.unop.fiber)
  map η := ofSheafSystemPresheafMap F J S η.unop
  map_id := (ofSheafSystemPresheaf_laws F J S).1
  map_comp := (ofSheafSystemPresheaf_laws F J S).2

/-- The component of a system morphism on sections over an object of `Grothendieck F`. -/
private def sheafSystemHomAppFiber {S T : SimplicialSites.SheafSystem
    (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)}
    (α : SimplicialSites.SheafSystem.Hom S T) (X : Grothendieck F) :
    (S.obj X.base.unop).obj.obj (op X.fiber) ⟶
      (T.obj X.base.unop).obj.obj (op X.fiber) :=
  (α.app X.base.unop).hom.app (op X.fiber)

/-- Assembly of a system of stage sheaves satisfies the total sheaf condition. -/
theorem ofSheafSystem_isSheaf (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)) :
    Presheaf.IsSheaf (topology F J) (ofSheafSystemPresheaf F J S) := by
  sorry

/-- The section components of a system morphism commute with the assembled restrictions. -/
private theorem ofSheafSystemMap_naturality {S T : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)} (α : SimplicialSites.SheafSystem.Hom S T)
    {W Z : (Grothendieck F)ᵒᵖ} (η : W ⟶ Z) :
    (ofSheafSystemPresheaf F J S).map η ≫ sheafSystemHomAppFiber F J α Z.unop =
      sheafSystemHomAppFiber F J α W.unop ≫ (ofSheafSystemPresheaf F J T).map η := by
  sorry

/-- Assemble a sheaf on the total site from a sheaf system. -/
def ofSheafSystem :
    SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ) ⥤ Sheaf (topology F J) (Type w) where
  obj S := ⟨ofSheafSystemPresheaf F J S, ofSheafSystem_isSheaf F J S⟩
  map {S T} α := ObjectProperty.homMk
    { app := fun W ↦ sheafSystemHomAppFiber F J α W.unop, naturality := fun _ _ η ↦ ofSheafSystemMap_naturality F J α η }
  map_id := by intro S; ext W x; rfl
  map_comp := by intro S T U α β; ext W x; rfl

/-- Sections of `ofSheafSystem.obj S` over `X` are the sections of `S.obj` at the fiber of `X`. -/
theorem ofSheafSystem_obj_app
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    (X : Grothendieck F) :
    ((ofSheafSystem F J).obj S).obj.obj (op X) =
      (S.obj X.base.unop).obj.obj (op X.fiber) :=
  rfl

/-- The identity on sections is natural from a total sheaf to its restriction and assembly. -/
private theorem unitIsoPresheaf_naturality (G : Sheaf (topology F J) (Type w))
    {W Z : (Grothendieck F)ᵒᵖ} (η : W ⟶ Z) :
    G.obj.map η ≫ 𝟙 _ = 𝟙 _ ≫ (((ofSheafSystem F J).obj ((toSheafSystem F J).obj G)).obj).map η := by
  sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
private def unitIsoPresheaf (G : Sheaf (topology F J) (Type w)) :
    G.obj ⟶ ((ofSheafSystem F J).obj ((toSheafSystem F J).obj G)).obj where
  app := fun _ ↦ 𝟙 _
  naturality := fun _ _ η ↦ unitIsoPresheaf_naturality F J G η

/-- The identity on sections is natural from restriction and assembly back to a total sheaf. -/
private theorem unitIsoPresheafInv_naturality (G : Sheaf (topology F J) (Type w))
    {W Z : (Grothendieck F)ᵒᵖ} (η : W ⟶ Z) :
    (((ofSheafSystem F J).obj ((toSheafSystem F J).obj G)).obj).map η ≫ 𝟙 _ = 𝟙 _ ≫ G.obj.map η := by
  sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
private def unitIsoPresheafInv (G : Sheaf (topology F J) (Type w)) :
    ((ofSheafSystem F J).obj ((toSheafSystem F J).obj G)).obj ⟶ G.obj where
  app := fun _ ↦ 𝟙 _
  naturality := fun _ _ η ↦ unitIsoPresheafInv_naturality F J G η

/-- The sectionwise identity comparison commutes with morphisms of total sheaves. -/
private theorem unitIso_naturality {G H : Sheaf (topology F J) (Type w)} (α : G ⟶ H) :
    α ≫ ObjectProperty.homMk (unitIsoPresheaf F J H) =
      ObjectProperty.homMk (unitIsoPresheaf F J G) ≫
        (toSheafSystem F J ⋙ ofSheafSystem F J).map α := by
  sorry

/-- The unit isomorphism of the sheaf-system equivalence, with identity components on sections. -/
def unitIso :
    𝟭 (Sheaf (topology F J) (Type w)) ≅ toSheafSystem F J ⋙ ofSheafSystem F J :=
  NatIso.ofComponents
    (fun G ↦
      { hom := ObjectProperty.homMk (unitIsoPresheaf F J G)
        inv := ObjectProperty.homMk (unitIsoPresheafInv F J G)
        hom_inv_id := by ext W x; rfl
        inv_hom_id := by ext W x; rfl })
    (fun α ↦ unitIso_naturality F J α)

/-- The identity on stage sections commutes with stage restrictions after assembly. -/
private theorem counitIsoHomApp_naturality (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)) (n : SimplexCategory)
    {V W : (F.obj (op n))ᵒᵖ} (η : V ⟶ W) :
    (((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).obj n).obj.map η ≫ 𝟙 _ = 𝟙 _ ≫ (S.obj n).obj.map η := by
  sorry

/-- Stagewise sheaf morphism from the assembled-then-restricted system back to `S`. -/
private def counitIsoHomApp
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    (n : SimplexCategory) :
    ((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).obj n ⟶ S.obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := fun _ _ η ↦ counitIsoHomApp_naturality F J S n η }

/-- The identity on stage sections commutes with stage restrictions after assembly. -/
private theorem counitIsoInvApp_naturality (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)) (n : SimplexCategory)
    {V W : (F.obj (op n))ᵒᵖ} (η : V ⟶ W) :
    (S.obj n).obj.map η ≫ 𝟙 _ = 𝟙 _ ≫ (((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).obj n).obj.map η := by
  sorry

/-- Stagewise sheaf morphism from `S` to the assembled-then-restricted system. -/
private def counitIsoInvApp
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    (n : SimplexCategory) :
    S.obj n ⟶ ((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := fun _ _ η ↦ counitIsoInvApp_naturality F J S n η }

/-- The stagewise comparison with restriction of assembly respects transitions and morphisms. -/
private theorem counitIso_laws :
    (∀ (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)) {m n : SimplexCategory} (φ : m ⟶ n),
      ((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).map φ ≫ (toposMap F J φ).pushforward.map (counitIsoHomApp F J S n) =
        counitIsoHomApp F J S m ≫ S.map φ) ∧
    (∀ (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)) {m n : SimplexCategory} (φ : m ⟶ n),
      S.map φ ≫ (toposMap F J φ).pushforward.map (counitIsoInvApp F J S n) =
        counitIsoInvApp F J S m ≫ ((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).map φ) ∧
    (∀ {S T : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)} (α : SimplicialSites.SheafSystem.Hom S T) (n : SimplexCategory),
      ((ofSheafSystem F J ⋙ toSheafSystem F J).map α).app n ≫ counitIsoHomApp F J T n =
        counitIsoHomApp F J S n ≫ α.app n) := by
  sorry

/-- The counit isomorphism of the sheaf-system equivalence, with identity components on stages. -/
def counitIso :
    ofSheafSystem F J ⋙ toSheafSystem F J ≅
      𝟭 (SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ toposMap F J φ)) :=
  NatIso.ofComponents
    (fun S ↦
      { hom := SimplicialSites.SheafSystem.homMk (counitIsoHomApp F J S) ((counitIso_laws F J).1 S)
        inv := SimplicialSites.SheafSystem.homMk (counitIsoInvApp F J S) ((counitIso_laws F J).2.1 S)
        hom_inv_id := by
          apply SimplicialSites.SheafSystem.Hom.ext
          intro n
          ext V x
          rfl
        inv_hom_id := by
          apply SimplicialSites.SheafSystem.Hom.ext
          intro n
          ext V x
          rfl })
    (fun α ↦ SimplicialSites.SheafSystem.Hom.ext ((counitIso_laws F J).2.2 α))

/-- Sheaves on the total site are equivalent to systems of stage sheaves with compatible
pushforward transitions. -/
def sheafEquivalence :
    Sheaf (topology F J) (Type w) ≌
      SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ toposMap F J φ) :=
  Equivalence.mk (toSheafSystem F J) (ofSheafSystem F J) (unitIso F J) (counitIso F J)

/-- The forward functor of `sheafEquivalence F J` extracts the system of degreewise restrictions
and `f_φ`-maps. -/
theorem sheafEquivalence_functor :
    (sheafEquivalence F J).functor = toSheafSystem F J :=
  rfl

/-- The inverse functor of `sheafEquivalence F J` assembles a sheaf on the total site from a
system `(F_n, F(φ))`. -/
theorem sheafEquivalence_inverse :
    (sheafEquivalence F J).inverse = ofSheafSystem F J :=
  rfl

end CategoryTheory.Grothendieck
