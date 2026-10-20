module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Definition 73.5.1: a smooth covering of an algebraic space `X` over a scheme `S`
is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}` of algebraic spaces over `S`
such that each `f_i` is smooth and `|X| = ⋃_i |f_i|(|X_i|)`, i.e. the morphisms
are jointly surjective. -/
@[stacks 041C] #check (AlgebraicGeometry.AlgebraicSpace.SmoothCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v}, (ι → CategoryTheory.Over X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.smoothCovering_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} (family : ι → Over X),
    SmoothCovering family ↔
      (∀ i, AlgebraicGeometry.AlgebraicSpace.Smooth (family i).hom) ∧
        Function.Surjective (smoothCoveringPointMap family))

#check (AlgebraicGeometry.AlgebraicSpace.SmoothCovering.covers_union :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v} (family : ι → Over X),
    SmoothCovering family ↔
      (∀ i, AlgebraicGeometry.AlgebraicSpace.Smooth (family i).hom) ∧
        (⋃ i, Set.range (Points.map (family i).hom)) = Set.univ)
