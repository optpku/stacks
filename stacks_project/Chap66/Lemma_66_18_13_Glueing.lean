/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_11

/-!
# Glueing sheaves on small étale sites of algebraic spaces

A sheaf of sets on `X_étale` determines a sheaf on `U_étale` for every object
`U` of `X_étale`, together with inverse-image transition isomorphisms along
morphisms of `X_étale`. This module packages those compatible systems.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing

variable {S : Scheme.{u}}

/-- The morphism of algebraic spaces induced by an identity in `Over S` is the identity. -/
theorem ofOverMap_id (U : Over S) : ofOverMap (𝟙 U) = 𝟙 (ofOver U) :=
  CategoryTheory.Functor.map_id yoneda U

/-- The morphism of algebraic spaces induced by a composite in `Over S` is the composite. -/
theorem ofOverMap_comp {U V W : Over S} (f : V ⟶ U) (g : W ⟶ V) :
    ofOverMap (g ≫ f) = ofOverMap g ≫ ofOverMap f :=
  CategoryTheory.Functor.map_comp yoneda g f

/-- The identity object of the small étale site of a scheme `U` over `S`. -/
def idObj (U : Over S) : smallEtaleSite (ofOver U) :=
  smallEtaleSite.mk (𝟙 (ofOver U))

/-- Pullback of Type-valued sheaves along a morphism of `X_étale`, as inverse image of
`f_small`. -/
noncomputable def pullback {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology (ofOver V.left)) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi (ofOverMap f.left)).inverseImage

/-- The triangle identity in `X_étale` as a morphism of algebraic spaces. -/
theorem ofOverMap_triangle {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    ofOverMap f.left ≫ U.hom = V.hom :=
  f.w.trans (Category.comp_id V.hom)

/-- A morphism of `X_étale` is étale as a morphism of algebraic spaces on the underlying
schemes. -/
instance etale_siteHom {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    Etale (ofOverMap f.left) :=
  sorry

/-- The underlying identity comparison used by `etaleRestrictionId`. -/
theorem etaleRestrictionId_hom (Y : AlgebraicSpace S) (U : smallEtaleSite Y) :
    (ofOverFunctor S).map (𝟙 U.left) ≫ U.hom =
      ((etaleRestriction (𝟙 Y)).obj U).hom :=
  sorry

/-- Restriction along an identity morphism is canonically the identity on the small étale
site. -/
noncomputable def etaleRestrictionId (Y : AlgebraicSpace S) :
    etaleRestriction (𝟙 Y) ≅ 𝟭 (smallEtaleSite Y) :=
  NatIso.ofComponents
    (fun U ↦
      MorphismProperty.CostructuredArrow.isoMk (Iso.refl U.left) trivial trivial
        (etaleRestrictionId_hom Y U))
    (fun _ ↦ sorry)

/-- Pullback along an identity is canonically isomorphic to the identity on small étale
sheaves. -/
noncomputable def pullbackId {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    pullback (𝟙 U) ≅ 𝟭 (Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1))) :=
  eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
      (ofOverMap_id U.left)) ≪≫
    smallEtaleMorphismOfTopoi_etaleRestrictionSheaf (𝟙 (ofOver U.left)) ≪≫
    Functor.sheafPushforwardContinuousId' (etaleRestrictionId (ofOver U.left))
      (Type (u + 1)) (smallEtaleTopology (ofOver U.left))

/-- Successive pullbacks of small étale sheaves are canonically isomorphic to pullback along
the composite. -/
noncomputable def pullbackComp {X : AlgebraicSpace S} {U V W : smallEtaleSite X}
    (f : V ⟶ U) (g : W ⟶ V) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  (smallEtaleMorphismOfTopoiComp (ofOverMap g.left) (ofOverMap f.left)).symm ≪≫
    eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
      (ofOverMap_comp f.left g.left).symm)

/-- A compatible system of sheaves on the small étale sites of schemes étale over an
algebraic space. -/
structure Object {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The sheaf on the small étale site of a scheme étale over `X`. -/
  obj (U : smallEtaleSite X) : Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1))
  /-- The inverse-image transition isomorphism `c_f : f_small⁻¹ F_U ≅ F_{U'}`. -/
  transition {U V : smallEtaleSite X} (f : V ⟶ U) : (pullback f).obj (obj U) ≅ obj V
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (U : smallEtaleSite X) :
    transition (𝟙 U) = (pullbackId U).app (obj U)
  /-- The transitions satisfy the inverse-image cocycle
  `c_g ∘ g_small⁻¹ c_f = c_{f ∘ g}`. -/
  transition_comp {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V) :
    (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
      (pullback g).mapIso (transition f) ≪≫ transition g

namespace Object

variable {X : AlgebraicSpace S}

/-- The fields of a compatible small-étale system express identity and the cocycle
condition for its transition isomorphisms. -/
theorem spec (F : Object X) :
    (∀ U : smallEtaleSite X, F.transition (𝟙 U) = (pullbackId U).app (F.obj U)) ∧
      (∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
        (pullbackComp f g).app (F.obj U) ≪≫ F.transition (g ≫ f) =
          (pullback g).mapIso (F.transition f) ≪≫ F.transition g) :=
  sorry

end Object

/-- A morphism of compatible small-étale systems is a componentwise sheaf morphism
commuting with every transition isomorphism. -/
@[ext]
structure Hom {X : AlgebraicSpace S} (F G : Object X) where
  /-- The component over an object of `X_étale`. -/
  app (U : smallEtaleSite X) : F.obj U ⟶ G.obj U
  /-- Component maps commute with inverse-image transitions. -/
  naturality {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (app U)) (F.transition f).hom (G.transition f).hom (app V)

namespace Hom

variable {X : AlgebraicSpace S}

/-- The identity compatible morphism. -/
def id (F : Object X) : Hom F F where
  app U := 𝟙 (F.obj U)
  naturality _ := sorry

/-- Composition of compatible morphisms. -/
def comp {F G H : Object X} (α : Hom F G) (β : Hom G H) : Hom F H where
  app U := α.app U ≫ β.app U
  naturality _ := sorry

end Hom

/-- The category of compatible systems, bundled without installing a global category
instance on the explicit object structure. -/
noncomputable def category (X : AlgebraicSpace S) : Cat :=
  { α := Object X
    str :=
      { Hom := Hom
        id := Hom.id
        comp := Hom.comp
        id_comp := sorry
        comp_id := sorry
        assoc := sorry } }

/-- The sheaf on `U_étale` obtained by inverse image along the structure morphism of
`U`. -/
noncomputable def fromSheafObj {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X) :
    Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi U.hom).inverseImage.obj F

/-- The canonical transition of the compatible system associated to a sheaf on
`X_étale`. -/
noncomputable def fromSheafTransition {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) {U V : smallEtaleSite X} (f : V ⟶ U) :
    (pullback f).obj (fromSheafObj F U) ≅ fromSheafObj F V :=
  ((smallEtaleMorphismOfTopoiComp (ofOverMap f.left) U.hom).app F).symm ≪≫
    eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage.obj F)
      (ofOverMap_triangle f))

namespace Object

variable {X : AlgebraicSpace S}

/-- The compatible system of small étale sheaves obtained by inverse image from a sheaf
on `X_étale`. -/
noncomputable def ofSheaf (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) : Object X where
  obj := fromSheafObj F
  transition := fromSheafTransition F
  transition_id _ := sorry
  transition_comp _ _ := sorry

end Object

/-- A morphism of sheaves on `X_étale` induces the componentwise compatible morphism
between their inverse-image systems. -/
noncomputable def fromSheafMap {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (η : F ⟶ G) :
    Hom (Object.ofSheaf F) (Object.ofSheaf G) where
  app U := (smallEtaleMorphismOfTopoi U.hom).inverseImage.map η
  naturality _ := sorry

/-- Inverse image of sheaves on `X_étale` to compatible systems on all `U_étale`. -/
noncomputable def fromSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ category X where
  obj := Object.ofSheaf
  map := fromSheafMap
  map_id := sorry
  map_comp := sorry

variable {X : AlgebraicSpace S}

/-- The object of the compatible system associated to a sheaf is inverse image along the
structure morphism. -/
theorem fromSheaf_obj (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (U : smallEtaleSite X) :
    ((fromSheaf X).obj F).obj U = (smallEtaleMorphismOfTopoi U.hom).inverseImage.obj F :=
  rfl

/-- The transition of the compatible system associated to a sheaf is the functoriality
isomorphism of inverse image. -/
theorem fromSheaf_transition (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((fromSheaf X).obj F).transition f = fromSheafTransition F f :=
  rfl

/-- The morphism in `U_étale` from the postcomposition of the identity object of `V` to
the identity object of `U`. -/
theorem idObjHom_w {U V : smallEtaleSite X} (f : V ⟶ U) :
    (ofOverFunctor S).map f.left ≫ (idObj U.left).hom =
      ((etaleRestriction (ofOverMap f.left)).obj (idObj V.left)).hom :=
  sorry

/-- The morphism in `U_étale` from the postcomposition of the identity object of `V` to
the identity object of `U`. -/
def idObjHom {U V : smallEtaleSite X} (f : V ⟶ U) :
    (etaleRestriction (ofOverMap f.left)).obj (idObj V.left) ⟶ idObj U.left :=
  MorphismProperty.CostructuredArrow.homMk f.left trivial (idObjHom_w f)

/-- Restriction of reconstructed global sections along a morphism of `X_étale`. -/
noncomputable def toSheafMap (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    (G.obj U).obj.obj (op (idObj U.left)) ⟶ (G.obj V).obj.obj (op (idObj V.left)) :=
  (G.obj U).obj.map (idObjHom f).op ≫
    (smallEtaleMorphismOfTopoi_inverseImage_obj (ofOverMap f.left) (G.obj U)
        (idObj V.left)).inv ≫
      (G.transition f).hom.hom.app (op (idObj V.left))

/-- The presheaf on `X_étale` reconstructed from terminal sections of a compatible
system. -/
noncomputable def toSheafPresheaf (G : Object X) : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1) where
  obj U := (G.obj U.unop).obj.obj (op (idObj U.unop.left))
  map f := toSheafMap G f.unop
  map_id := sorry
  map_comp := sorry

/-- The reconstructed presheaf of a compatible system is a sheaf on `X_étale`. -/
theorem toSheaf_isSheaf (G : Object X) :
    Presheaf.IsSheaf (smallEtaleTopology X) (toSheafPresheaf G) :=
  sorry

/-- Reconstruction of a sheaf on `X_étale` from a compatible system of sheaves on all
`U_étale`. -/
noncomputable def toSheaf (X : AlgebraicSpace S) :
    category X ⥤ Sheaf (smallEtaleTopology X) (Type (u + 1)) where
  obj G := ⟨toSheafPresheaf G, toSheaf_isSheaf G⟩
  map {G H} α :=
    ObjectProperty.homMk
      { app U := (α.app U.unop).hom.app (op (idObj U.unop.left))
        naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Reconstructed sections of a compatible system at `U` are the sections of `F_U` at the
identity object of `U_étale`. -/
theorem toSheaf_obj (G : Object X) (U : smallEtaleSite X) :
    ((toSheaf X).obj G).obj.obj (op U) = (G.obj U).obj.obj (op (idObj U.left)) :=
  rfl

/-- Inverse image from sheaves on `X_étale` to compatible systems on all small étale sites
is an equivalence of categories. -/
instance fromSheaf_isEquivalence (X : AlgebraicSpace S) :
    (fromSheaf X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing
