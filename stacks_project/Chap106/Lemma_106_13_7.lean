/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Etale
import StacksCheckRecall

/-!
# Cartesian squares over well-nigh affine moduli spaces

An étale separated morphism of algebraic stacks that induces isomorphisms on
automorphism groups at points, with well-nigh affine target, fits in a
2-cartesian square whose bottom arrow is a separated étale morphism of
schemes into the affine-scheme moduli space of Lemma 106.13.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/- Lemma 106.13.7. Let `h : X' ⟶ X` be a morphism of algebraic stacks. Assume
`X` is well-nigh affine, `h` is étale, `h` is separated, and `h` induces
isomorphisms on automorphism groups at every point of `|X'|` (Remark 101.19.5).
If `f : X ⟶ M.toGroupoids` is a uniform categorical moduli space in the
category of affine schemes as in Lemma 106.13.4, then there exist a scheme
`M'` over the base, a morphism `f' : X' ⟶ (AlgebraicSpace.ofOver M').toGroupoids`,
a separated étale morphism `g : AlgebraicSpace.ofOver M' ⟶ M`, and a 2-cell
making the displayed square cartesian. -/
@[stacks 0DUS]
#check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.exists_cartesian_separated_etale_scheme :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [IsWellNighAffine X]
    (h : X' ⟶ X) [Etale h] [Separated h]
    (h_isoAt : ∀ x : |X'|, automorphismGroup.IsIsoAt h x)
    {M : AlgebraicSpace S} (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f],
    ∃ (M' : Over S) (f' : X' ⟶ (AlgebraicSpace.ofOver M').toGroupoids)
      (g : AlgebraicSpace.ofOver M' ⟶ M)
      (α : h ≫ f ≅ f' ≫ AlgebraicSpace.toGroupoids.map g),
      AlgebraicSpace.Etale g ∧ AlgebraicSpace.Separated g ∧
        (PseudoPullbackCone.mk f (AlgebraicSpace.toGroupoids.map g)
          X' h f' α).IsBilimit)

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine
