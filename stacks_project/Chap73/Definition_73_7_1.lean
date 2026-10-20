module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Definition 73.7.1: let `S` be a scheme, and let `X` be an algebraic space over `S`.
An fppf covering of `X` is a family of morphisms `{fᵢ : Xᵢ ⟶ X}` of algebraic spaces
over `S` such that each `fᵢ` is `Flat` and `LocallyOfFinitePresentation` and such that
`|X| = ⋃ᵢ |fᵢ|(|Xᵢ|)`, i.e., the morphisms are jointly surjective. -/
@[stacks 03Y8] #check (AlgebraicGeometry.AlgebraicSpace.FppfCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : AlgebraicGeometry.AlgebraicSpace S} (Xi : ι → AlgebraicGeometry.AlgebraicSpace S),
    (∀ i, Xi i ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.FppfCover.{u, v} :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    AlgebraicGeometry.AlgebraicSpace S → Type (max (u + 1) (v + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.FppfCovering.source_spec :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : AlgebraicGeometry.AlgebraicSpace S} (Xi : ι → AlgebraicGeometry.AlgebraicSpace S)
    (f : ∀ i, Xi i ⟶ X) [AlgebraicGeometry.AlgebraicSpace.FppfCovering Xi f],
    (∀ i, AlgebraicGeometry.AlgebraicSpace.Flat (f i)) ∧
      (∀ i, AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation (f i)) ∧
        ⋃ i, Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map (f i)) = Set.univ)
