module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction

/-!
# Identity charts in small étale presentations

A scheme over the base has a canonical identity chart. Morphisms in a small étale
presentation induce arrows from the postcomposition of these identity charts. These
actual site objects and arrows support reconstruction of both sheaves and modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

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

/-- The triangle identity in `X_étale` as a morphism of algebraic spaces. -/
theorem ofOverMap_triangle {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    ofOverMap f.left ≫ U.hom = V.hom :=
  f.w.trans (Category.comp_id V.hom)

/-- A morphism of `X_étale` is étale as a morphism of algebraic spaces on the underlying
schemes. -/
instance etale_siteHom {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    Etale (ofOverMap f.left) :=
  sorry

variable {X : AlgebraicSpace S}

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

end AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing
