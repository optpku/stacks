module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Finite type morphisms of algebraic spaces

A morphism of algebraic spaces is locally of finite type when every étale
scheme square over it has locally-of-finite-type top arrow. It is of finite
type when it is locally of finite type and quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is locally of finite
type if every commutative square with étale vertical arrows from schemes has
locally-of-finite-type top arrow. -/
class LocallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has locally-of-finite-type top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfFiniteType h.left

/-- A morphism of algebraic spaces is locally of finite type if and only if
every commutative square with étale vertical arrows from schemes has
locally-of-finite-type top arrow. -/
theorem locallyOfFiniteType_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfFiniteType h.left :=
  sorry

namespace LocallyOfFiniteType

/-- An étale scheme square over a locally-of-finite-type morphism of algebraic
spaces has locally-of-finite-type top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfFiniteType h.left :=
  sorry

/-- The identity morphism of an algebraic space is locally of finite type. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    LocallyOfFiniteType (𝟙 X) :=
  sorry

/-- A representable morphism of algebraic spaces with the relative
locally-of-finite-type property is locally of finite type. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.LocallyOfFiniteType :
          MorphismProperty Scheme.{u})).presheaf f) :
    LocallyOfFiniteType f :=
  sorry

end LocallyOfFiniteType

/-- A morphism of algebraic spaces is of finite type if it is quasi-compact and
locally of finite type. -/
@[mk_iff]
class FiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends QuasiCompact f, LocallyOfFiniteType f

namespace FiniteType

/-- The identity morphism of an algebraic space is of finite type. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : FiniteType (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is of finite type. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : FiniteType f :=
  sorry

/-- A quasi-compact morphism that is locally of finite type is of finite type. -/
instance instOfQuasiCompactLocallyOfFiniteType {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f]
    [LocallyOfFiniteType f] : FiniteType f :=
  sorry

end FiniteType

end AlgebraicGeometry.AlgebraicSpace
