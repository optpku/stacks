/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Adjunction.KanExtension
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_3_4_System
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise

/-!
# Sheaves on the total site of a fiberwise simplicial site

Comparison functors between `Sh(Grothendieck F)` and the category of sheaf systems attached
to the morphisms of topoi `f_φ` of a cocontinuous simplex diagram of sites.
-/

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
    NatIso.ofComponents (fun P ↦ (sheafificationIso P).symm) sorry

/-- Direct images of `f_id` identify with the identity functor on `Sh(C n)` by uniqueness of
right adjoints along `toposMap_inverseImage_id`. -/
def toposMap_pushforward_id (n : SimplexCategory) :
    (toposMap F J (𝟙 n)).pushforward ≅ 𝟭 (Sheaf (J (op n)).toGrothendieck (Type w)) :=
  Adjunction.rightAdjointUniq
    ((toposMap F J (𝟙 n)).adjunction.ofNatIsoLeft (toposMap_inverseImage_id F J n))
    Adjunction.id

/-- Pushforwards of `toposMap F J` are unital and strictly functorial in simplex operators. -/
instance instHasPushforwardFunctoriality_toposMap :
    SimplicialSites.HasPushforwardFunctoriality
      (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ) where
  pushforwardIdIso n := toposMap_pushforward_id F J n
  pushforwardCompIso ψ φ := toposMap_pushforward_comp F J ψ φ

/-- Restriction of a sheaf on the total site to the fiber `F.obj (op n)`. -/
def restrictToDegree (n : SimplexCategory) :
    Sheaf (topology F J) (Type w) ⥤ Sheaf (J (op n)).toGrothendieck (Type w) where
  obj G := ⟨(ι F (op n)).op ⋙ G.obj, sorry⟩
  map {G H} α := ObjectProperty.homMk
    { app := fun V ↦ α.hom.app ((ι F (op n)).op.obj V), naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The underlying presheaf of `restrictToDegree n` is composition with `(ι F (op n)).op`. -/
theorem restrictToDegree_obj (n : SimplexCategory) (G : Sheaf (topology F J) (Type w)) :
    ((restrictToDegree F J n).obj G).obj = (ι F (op n)).op ⋙ G.obj :=
  sorry

/-- The total-category arrow `(φ, 𝟙) : V ⟶ u_φ(V)` along which `F(φ)` is restriction. -/
def stageHom {m n : SimplexCategory} (φ : m ⟶ n) (V : F.obj (op n)) :
    (ι F (op n)).obj V ⟶ (ι F (op m)).obj ((F.map φ.op).toFunctor.obj V) :=
  Hom.mk φ.op (𝟙 ((F.map φ.op).toFunctor.obj V))

/-- Presheaf-level transition of `toSheafSystem` at `φ`, the Ran mate of restriction along
`stageHom φ`. -/
def toSheafSystemMapPresheaf (G : Sheaf (topology F J) (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((restrictToDegree F J m).obj G).obj ⟶
      ((toposMap F J φ).pushforward.obj ((restrictToDegree F J n).obj G)).obj :=
  ((F.map φ.op).toFunctor.op.ranAdjunction (Type w)).homEquiv
      ((restrictToDegree F J m).obj G).obj ((restrictToDegree F J n).obj G).obj
    { app := fun V ↦ G.obj.map (stageHom F φ V.unop).op, naturality := sorry }

/-- The transition of `toSheafSystem` at `φ` is the sheaf morphism associated to the Ran mate of
restriction along `stageHom φ`. -/
def toSheafSystemMap (G : Sheaf (topology F J) (Type w)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictToDegree F J m).obj G ⟶
      (toposMap F J φ).pushforward.obj ((restrictToDegree F J n).obj G) :=
  ObjectProperty.homMk (toSheafSystemMapPresheaf F J G φ)

/-- Extract the sheaf system of degreewise restrictions from a sheaf on the total site. -/
def toSheafSystem :
    Sheaf (topology F J) (Type w) ⥤
      SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ toposMap F J φ) where
  obj G :=
    SimplicialSites.SheafSystem.of (fun n ↦ (restrictToDegree F J n).obj G)
      (fun {m n} φ ↦ toSheafSystemMap F J G φ) sorry sorry
  map {G H} α :=
    SimplicialSites.SheafSystem.homMk (fun n ↦ (restrictToDegree F J n).map α) sorry
  map_id := sorry
  map_comp := sorry

/-- The stage sheaf of `toSheafSystem.obj G` at `n` is the restriction of `G` to `F.obj (op n)`. -/
theorem toSheafSystem_obj_obj (G : Sheaf (topology F J) (Type w)) (n : SimplexCategory) :
    ((toSheafSystem F J).obj G).obj n = (restrictToDegree F J n).obj G :=
  sorry

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

/-- The assembled presheaf on `Grothendieck F` associated to a sheaf system. -/
def ofSheafSystemPresheaf
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ)) :
    (Grothendieck F)ᵒᵖ ⥤ Type w where
  obj W := (S.obj W.unop.base.unop).obj.obj (op W.unop.fiber)
  map {W Z} η := ofSheafSystemPresheafMap F J S η.unop
  map_id := sorry
  map_comp := sorry

/-- The component of a system morphism on sections over an object of `Grothendieck F`. -/
def sheafSystemHomAppFiber {S T : SimplicialSites.SheafSystem
    (fun n ↦ (J (op n)).toGrothendieck) (fun φ ↦ toposMap F J φ)}
    (α : SimplicialSites.SheafSystem.Hom S T) (X : Grothendieck F) :
    (S.obj X.base.unop).obj.obj (op X.fiber) ⟶
      (T.obj X.base.unop).obj.obj (op X.fiber) :=
  (α.app X.base.unop).hom.app (op X.fiber)

/-- Assemble a sheaf on the total site from a sheaf system. -/
def ofSheafSystem :
    SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ) ⥤ Sheaf (topology F J) (Type w) where
  obj S := ⟨ofSheafSystemPresheaf F J S, sorry⟩
  map {S T} α := ObjectProperty.homMk
    { app := fun W ↦ sheafSystemHomAppFiber F J α W.unop, naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Sections of `ofSheafSystem.obj S` over `X` are the sections of `S.obj` at the fiber of `X`. -/
theorem ofSheafSystem_obj_app
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    (X : Grothendieck F) :
    ((ofSheafSystem F J).obj S).obj.obj (op X) =
      (S.obj X.base.unop).obj.obj (op X.fiber) :=
  sorry

/-- Component of the unit isomorphism on underlying presheaves. -/
def unitIsoPresheaf (G : Sheaf (topology F J) (Type w)) :
    G.obj ⟶ ((ofSheafSystem F J).obj ((toSheafSystem F J).obj G)).obj where
  app := fun _ ↦ 𝟙 _
  naturality := sorry

/-- Component of the inverse unit isomorphism on underlying presheaves. -/
def unitIsoPresheafInv (G : Sheaf (topology F J) (Type w)) :
    ((ofSheafSystem F J).obj ((toSheafSystem F J).obj G)).obj ⟶ G.obj where
  app := fun _ ↦ 𝟙 _
  naturality := sorry

/-- The unit isomorphism of the sheaf-system equivalence, with identity components on sections. -/
def unitIso :
    𝟭 (Sheaf (topology F J) (Type w)) ≅ toSheafSystem F J ⋙ ofSheafSystem F J :=
  NatIso.ofComponents
    (fun G ↦
      { hom := ObjectProperty.homMk (unitIsoPresheaf F J G)
        inv := ObjectProperty.homMk (unitIsoPresheafInv F J G)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Stagewise sheaf morphism from the assembled-then-restricted system back to `S`. -/
def counitIsoHomApp
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    (n : SimplexCategory) :
    ((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).obj n ⟶ S.obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }

/-- Stagewise sheaf morphism from `S` to the assembled-then-restricted system. -/
def counitIsoInvApp
    (S : SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ toposMap F J φ))
    (n : SimplexCategory) :
    S.obj n ⟶ ((ofSheafSystem F J ⋙ toSheafSystem F J).obj S).obj n :=
  ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }

/-- The counit isomorphism of the sheaf-system equivalence, with identity components on stages. -/
def counitIso :
    ofSheafSystem F J ⋙ toSheafSystem F J ≅
      𝟭 (SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ toposMap F J φ)) :=
  NatIso.ofComponents
    (fun S ↦
      { hom := SimplicialSites.SheafSystem.homMk (counitIsoHomApp F J S) sorry
        inv := SimplicialSites.SheafSystem.homMk (counitIsoInvApp F J S) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end CategoryTheory.Grothendieck
