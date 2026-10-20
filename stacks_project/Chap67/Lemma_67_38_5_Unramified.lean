module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local

/-!
# Pointwise unramifiedness of morphisms of algebraic spaces

A morphism of algebraic spaces is unramified at a point when it is unramified
after restriction to an open subspace neighbourhood, in the sense of Stacks
Definition 67.38.1 (2). The remaining predicates package the equivalent
characterizations of unramified morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.UnramifiedAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.unramifiedAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    UnramifiedAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Unramified (i ≫ f))

end AlgebraicGeometry.AlgebraicSpace
