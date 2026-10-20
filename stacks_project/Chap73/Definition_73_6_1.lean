module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 73.6.1: a syntomic covering of an algebraic space `X` over a scheme `S`
is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}` of algebraic spaces over `S`
such that each `f_i` is syntomic and `|X| = ⋃_i |f_i|(|X_i|)`, i.e. the morphisms
are jointly surjective. -/
@[stacks 041A] #check (AlgebraicGeometry.AlgebraicSpace.SyntomicCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v}, (ι → CategoryTheory.Over X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.syntomicCovering_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v} (family : ι → CategoryTheory.Over X),
    AlgebraicGeometry.AlgebraicSpace.SyntomicCovering family ↔
      (∀ i, AlgebraicGeometry.AlgebraicSpace.Syntomic (family i).hom) ∧
        Function.Surjective (AlgebraicGeometry.AlgebraicSpace.syntomicCoveringPointMap family))

#check (AlgebraicGeometry.AlgebraicSpace.SyntomicCovering.covers_union :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v} (family : ι → CategoryTheory.Over X),
    AlgebraicGeometry.AlgebraicSpace.SyntomicCovering family ↔
      (∀ i, AlgebraicGeometry.AlgebraicSpace.Syntomic (family i).hom) ∧
        (⋃ i, Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map (family i).hom)) = Set.univ)
