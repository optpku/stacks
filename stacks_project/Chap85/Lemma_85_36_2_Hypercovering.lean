module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperHypercovering

/-! # Proper hypercoverings of algebraic spaces -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Functor
open scoped Simplicial

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.IsProperHypercovering :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    {U : SimplicialObject (AlgebraicSpace S)} →
      (U ⟶ (const SimplexCategoryᵒᵖ).obj X) → Prop)
