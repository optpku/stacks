module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap101.Lemma_101_36_4_Etale
public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup
public import stacks_project.Chap106.Lemma_106_13_4

/-!
# Étale cartesian moduli spaces of well-nigh affine stacks

An étale morphism of well-nigh affine algebraic stacks that induces
isomorphisms on automorphism groups at points fits in a 2-cartesian square
whose vertical arrows are the affine-scheme moduli spaces of Lemma 106.13.4
and whose bottom arrow is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- Lemma 106.13.5. Let `h : X' ⟶ X` be a morphism of well-nigh affine algebraic
stacks. If `h` is étale and induces isomorphisms on automorphism groups at
every point of `|X'|` (Remark 101.19.5), and if `f : X ⟶ M.toGroupoids` is a
uniform categorical moduli space in the category of affine schemes as in
Lemma 106.13.4, then there exist an algebraic space `M'`, a uniform
categorical moduli space `f' : X' ⟶ M'.toGroupoids` in the category of affine
schemes, an étale morphism `g : M' ⟶ M`, and a 2-cell making the displayed
square cartesian. -/
@[stacks 0DUQ]
theorem exists_cartesian_etale_moduliSpace
    {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X']
    [IsWellNighAffine X] [IsWellNighAffine X']
    (h : X' ⟶ X) [Etale h]
    (h_isoAt : ∀ x : |X'|, automorphismGroup.IsIsoAt h x)
    {M : AlgebraicSpace S} (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f] :
    ∃ (M' : AlgebraicSpace S) (f' : X' ⟶ M'.toGroupoids) (g : M' ⟶ M)
      (α : h ≫ f ≅ f' ≫ AlgebraicSpace.toGroupoids.map g),
      IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f' ∧
        AlgebraicSpace.Etale g ∧
          (PseudoPullbackCone.mk f (AlgebraicSpace.toGroupoids.map g)
            X' h f' α).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine
