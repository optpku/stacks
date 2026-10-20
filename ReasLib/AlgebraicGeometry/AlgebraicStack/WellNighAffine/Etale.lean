module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Moduli
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Separated étale morphisms over well-nigh affine stacks

Stabilizer-preserving separated étale morphisms over a well-nigh affine stack
are obtained by base change from separated étale morphisms of schemes over its
affine uniform categorical moduli space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- Let `h : X' ⟶ X` be a separated étale morphism of algebraic stacks that
induces isomorphisms on automorphism groups at every point, with `X` well-nigh
affine. For any uniform categorical moduli morphism `f : X ⟶ M.toGroupoids`
in the category of affine schemes, there exist a scheme `M'` over the base,
a morphism from `X'` to `M'`, and a separated étale morphism from `M'` to `M`
forming a 2-cartesian square with `h` and `f`. -/
@[stacks 0DUS]
theorem exists_cartesian_separated_etale_scheme
    {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [IsWellNighAffine X]
    (h : X' ⟶ X) [Etale h] [Separated h]
    (h_isoAt : ∀ x : |X'|, automorphismGroup.IsIsoAt h x)
    {M : AlgebraicSpace S} (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f] :
    ∃ (M' : Over S) (f' : X' ⟶ (AlgebraicSpace.ofOver M').toGroupoids)
      (g : AlgebraicSpace.ofOver M' ⟶ M)
      (α : h ≫ f ≅ f' ≫ AlgebraicSpace.toGroupoids.map g),
      AlgebraicSpace.Etale g ∧ AlgebraicSpace.Separated g ∧
        (PseudoPullbackCone.mk f (AlgebraicSpace.toGroupoids.map g)
          X' h f' α).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine
