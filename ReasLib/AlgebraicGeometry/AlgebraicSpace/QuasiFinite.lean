module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Quasi-finite morphisms of algebraic spaces

A quasi-finite morphism is of finite type and chartwise locally quasi-finite.
The chartwise locally quasi-finite predicate alone does not require local finite
type; the finite-type condition supplies this requirement and quasi-compactness.
The conjunction of local finite type and chartwise local quasi-finiteness has an
étale scheme-square characterization. Quasi-finiteness at a point means that
this conjunction holds after restriction to an open neighbourhood of the point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is quasi-finite if it is of finite type and
locally quasi-finite. -/
class QuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends FiniteType f where
  /-- A quasi-finite morphism is locally quasi-finite. -/
  [locallyQuasiFinite : LocallyQuasiFinite f]

/-- A morphism of algebraic spaces is quasi-finite if and only if it is of
finite type and locally quasi-finite. -/
theorem quasiFinite_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : QuasiFinite f ↔ FiniteType f ∧ LocallyQuasiFinite f :=
  ⟨fun h ↦ ⟨h.toFiniteType, h.locallyQuasiFinite⟩,
    fun ⟨hft, hlq⟩ ↦ { toFiniteType := hft, locallyQuasiFinite := hlq }⟩

namespace QuasiFinite

/-- The identity morphism of an algebraic space is quasi-finite. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : QuasiFinite (𝟙 X) where
  toFiniteType := inferInstance
  locallyQuasiFinite := inferInstance

/-- An isomorphism of algebraic spaces is quasi-finite. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : QuasiFinite f :=
  sorry

/-- A finite type locally quasi-finite morphism of algebraic spaces is
quasi-finite. -/
instance instOfFiniteTypeLocallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    [LocallyQuasiFinite f] : QuasiFinite f where
  toFiniteType := inferInstance
  locallyQuasiFinite := inferInstance

end QuasiFinite

namespace FiniteType

/-- A morphism of algebraic spaces is locally of finite type and locally
quasi-finite if and only if every commutative square with étale vertical arrows
from schemes has locally-of-finite-type and locally quasi-finite top arrow. -/
theorem locallyQuasiFinite_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfFiniteType h.left ∧
                AlgebraicGeometry.LocallyQuasiFinite h.left :=
  sorry

/-- An étale scheme square over a locally of finite type and locally
quasi-finite morphism of algebraic spaces has locally-of-finite-type and
locally quasi-finite top arrow. -/
theorem locallyQuasiFinite_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfFiniteType h.left ∧
      AlgebraicGeometry.LocallyQuasiFinite h.left :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces is quasi-finite at a point `x`
of `|X|` if some open neighbourhood of `x` has locally of finite type and
locally quasi-finite restriction. -/
def QuasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      LocallyOfFiniteType (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f)

/-- Quasi-finiteness at a point in the finite-type sense is the existence of an
open subspace neighbourhood on which the morphism is locally of finite type and
locally quasi-finite. -/
theorem quasiFiniteAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    QuasiFiniteAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyOfFiniteType (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f) :=
  sorry

namespace QuasiFiniteAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is locally of
finite type and locally quasi-finite witnesses that `f` is quasi-finite at
every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [LocallyOfFiniteType (i ≫ f)] [LocallyQuasiFinite (i ≫ f)] :
    QuasiFiniteAt f x :=
  sorry

end QuasiFiniteAt

/-- A locally of finite type and locally quasi-finite morphism of algebraic
spaces is quasi-finite at every point of its source. -/
theorem quasiFiniteAt_of_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (x : Points X) : QuasiFiniteAt f x :=
  sorry

end FiniteType

end AlgebraicGeometry.AlgebraicSpace
