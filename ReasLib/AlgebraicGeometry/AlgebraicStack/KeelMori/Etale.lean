module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KeelMori
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Étale morphisms between moduli spaces of algebraic stacks

Stabilizer-preserving separated étale morphisms of algebraic stacks with finite
inertia induce separated étale morphisms of their uniform categorical moduli
spaces, and the resulting squares are 2-cartesian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An étale separated morphism of algebraic stacks inducing isomorphisms on
automorphism groups, whose target has finite inertia, induces a separated étale
morphism of uniform categorical moduli algebraic spaces, with a 2-cartesian
square. -/
@[stacks 0DUV]
theorem exists_cartesian_separated_etale_moduliSpace
    {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X']
    [IsFinite (forget.{u + 1, u, u, u + 1} X)]
    (h : X' ⟶ X) [Etale h] [Separated h]
    (h_isoAt : ∀ x : |X'|, automorphismGroup.IsIsoAt h x)
    {M : AlgebraicSpace S} (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpace f] :
    ∃ (M' : AlgebraicSpace S) (f' : X' ⟶ M'.toGroupoids) (g : M' ⟶ M)
      (α : h ≫ f ≅ f' ≫ AlgebraicSpace.toGroupoids.map g),
      IsUniformCategoricalModuliSpace f' ∧ AlgebraicSpace.Etale g ∧
        AlgebraicSpace.Separated g ∧
          (PseudoPullbackCone.mk f (AlgebraicSpace.toGroupoids.map g)
            X' h f' α).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack
