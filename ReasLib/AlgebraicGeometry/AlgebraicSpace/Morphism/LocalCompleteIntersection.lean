module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
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

/-- A representable morphism of algebraic spaces with the relative
local-complete-intersection property is a local complete intersection. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection :
          MorphismProperty Scheme.{u})).presheaf f) :
    IsLocalCompleteIntersection f :=
  sorry

end IsLocalCompleteIntersection

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Koszul at a point `x` of `X`
if it is a local complete intersection after restriction to some open subspace
neighbourhood of `x`. -/
def KoszulAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      IsLocalCompleteIntersection (i ≫ f)

/-- Koszulness at a point is the existence of an open subspace neighbourhood on
which the morphism is a local complete intersection. -/
theorem koszulAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    KoszulAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          IsLocalCompleteIntersection (i ≫ f) :=
  sorry

namespace KoszulAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is a local complete
intersection witnesses that `f` is Koszul at every point of the image of
`|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [IsLocalCompleteIntersection (i ≫ f)] : KoszulAt f x :=
  sorry

end KoszulAt

/-- A local complete intersection morphism of algebraic spaces is Koszul at
every point of its source. -/
theorem koszulAt_of_isLocalCompleteIntersection {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f]
    (x : Points X) : KoszulAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
