module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Local complete intersection morphisms of algebraic spaces

A morphism of algebraic spaces is a local complete intersection (Koszul)
morphism when every étale scheme square over it has local-complete-intersection
top arrow, in the sense of Stacks Definition 76.48.1 (1). Pointwise Koszulness
is local-complete-intersection after restriction to an open subspace
neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isLocalCompleteIntersection_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    IsLocalCompleteIntersection f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfType
                RingHom.IsLocalCompleteIntersection h.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b),
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsLocalCompleteIntersection (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.of_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection :
          MorphismProperty Scheme.{u})).presheaf f),
    IsLocalCompleteIntersection f)

#check (AlgebraicGeometry.AlgebraicSpace.KoszulAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.koszulAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    KoszulAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          IsLocalCompleteIntersection (i ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.KoszulAt.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [IsLocalCompleteIntersection (i ≫ f)], KoszulAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.koszulAt_of_isLocalCompleteIntersection :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f]
    (x : Points X), KoszulAt f x)

end AlgebraicGeometry.AlgebraicSpace
