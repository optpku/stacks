module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

/-!
# Syntomic morphisms of algebraic spaces

Syntomicity of a morphism of algebraic spaces is tested on étale scheme
squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is syntomic when every
commutative square with étale vertical arrows from schemes has syntomic top
arrow. -/
class Syntomic {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has syntomic top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Syntomic h.left

/-- A morphism of algebraic spaces is syntomic exactly when every étale scheme
square over it has syntomic top arrow. -/
theorem syntomic_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Syntomic f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Syntomic h.left := sorry

namespace Syntomic

/-- An étale scheme square over a syntomic morphism of algebraic spaces has
syntomic top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Syntomic f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Syntomic h.left := sorry

/-- The identity morphism of an algebraic space is syntomic. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Syntomic (𝟙 X) := sorry

end Syntomic

end AlgebraicGeometry.AlgebraicSpace
