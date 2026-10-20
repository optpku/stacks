/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Moduli
public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Uniform categorical moduli spaces of well-nigh affine stacks

A well-nigh affine algebraic stack admits a uniform categorical moduli space in
the category of affine schemes. This moduli morphism also satisfies the uniform
categorical universal property for all algebraic spaces and is separated,
quasi-compact, and a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- A well-nigh affine algebraic stack admits a uniform categorical moduli space
in the category of affine schemes. -/
@[stacks 0DUP]
theorem exists_isUniformCategoricalModuliSpaceIn_isAffine
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsWellNighAffine X] :
    ∃ (M : AlgebraicSpace S) (f : X ⟶ M.toGroupoids),
      IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f :=
  sorry

/-- A uniform categorical moduli morphism from a well-nigh affine algebraic
stack to an affine algebraic space is separated. -/
@[stacks 0DUP, instance]
instance instSeparated {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f] :
    Separated f :=
  sorry

/-- A uniform categorical moduli morphism from a well-nigh affine algebraic
stack to an affine algebraic space is quasi-compact. -/
@[stacks 0DUP, instance]
instance instQuasiCompact {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f] :
    QuasiCompact f :=
  sorry

/-- A uniform categorical moduli morphism from a well-nigh affine algebraic
stack to an affine algebraic space is a universal homeomorphism. -/
@[stacks 0DUP, instance]
instance instUniversalHomeomorphism {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f] :
    UniversalHomeomorphism f :=
  sorry

/-- A uniform categorical moduli morphism in the category of affine schemes
from a well-nigh affine algebraic stack is a uniform categorical moduli morphism
for all algebraic spaces. -/
@[stacks 0DUR, instance]
instance instIsUniformCategoricalModuliSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn AlgebraicSpace.IsAffine f] :
    IsUniformCategoricalModuliSpace f :=
  sorry

/-- An étale morphism between well-nigh affine algebraic stacks that induces
isomorphisms on automorphism groups at every point induces an étale morphism
between their affine uniform categorical moduli spaces, and the resulting
square is 2-cartesian. -/
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
