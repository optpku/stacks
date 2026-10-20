module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite

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

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.locallyQuasiFinite_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfFiniteType h.left ∧
                AlgebraicGeometry.LocallyQuasiFinite h.left)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.locallyQuasiFinite_spec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b),
    AlgebraicGeometry.LocallyOfFiniteType h.left ∧
      AlgebraicGeometry.LocallyQuasiFinite h.left)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.QuasiFiniteAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.quasiFiniteAt_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X),
    QuasiFiniteAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyOfFiniteType (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.QuasiFiniteAt.of :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [LocallyOfFiniteType (i ≫ f)] [LocallyQuasiFinite (i ≫ f)],
    QuasiFiniteAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteType.quasiFiniteAt_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (x : Points X), QuasiFiniteAt f x)

end FiniteType

end AlgebraicGeometry.AlgebraicSpace
