module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection

/-!
# Local complete intersection morphisms of algebraic spaces

Local complete intersection morphisms of algebraic spaces are tested on étale
scheme squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is a local complete
intersection morphism when every commutative square with étale vertical arrows
from schemes has local-complete-intersection top arrow. -/
class IsLocalCompleteIntersection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has local-complete-intersection top
  arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h.left

/-- A morphism of algebraic spaces is a local complete intersection exactly
when every étale scheme square over it has local-complete-intersection top
arrow. -/
theorem isLocalCompleteIntersection_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsLocalCompleteIntersection f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfType
                RingHom.IsLocalCompleteIntersection h.left := sorry

namespace IsLocalCompleteIntersection

/-- An étale scheme square over a local complete intersection morphism of
algebraic spaces has local-complete-intersection top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h.left := sorry

/-- The identity morphism of an algebraic space is a local complete
intersection. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsLocalCompleteIntersection (𝟙 X) := sorry

end IsLocalCompleteIntersection

end AlgebraicGeometry.AlgebraicSpace
