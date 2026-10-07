module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Stacks locally quasi-finite morphisms of algebraic spaces

Stacks locally quasi-finite morphisms are the conjunction of locally of
finite type and locally quasi-finite. This file records that conjunction
through étale scheme squares, and the corresponding pointwise predicate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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
