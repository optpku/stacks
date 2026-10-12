/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap106.Definition_106_12_1_Moduli

/-!
# Affine-flat recognition of uniform categorical moduli spaces

A morphism from an algebraic stack to an algebraic space is a uniform
categorical moduli space as soon as every base change along a flat morphism
from an affine scheme is a categorical moduli space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.12.4. Let `f : X ⟶ Y.toGroupoids` be a morphism from an algebraic
stack to an algebraic space. If for every affine scheme `Y'` and every flat
morphism `g : AlgebraicSpace.ofOver Y' ⟶ Y` the base change
`pullbackSnd f g` is a categorical moduli space, then `f` is a uniform
categorical moduli space. -/
@[stacks 0DUJ]
theorem IsUniformCategoricalModuliSpace.of_forall_affine
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids)
    (hf : ∀ (Y' : Over S) [IsAffine Y'.left]
      (g : AlgebraicSpace.ofOver Y' ⟶ Y) [AlgebraicSpace.Flat g],
      IsCategoricalModuliSpace (pullbackSnd f g)) :
    IsUniformCategoricalModuliSpace f :=
  sorry

/-- A morphism from an algebraic stack to an algebraic space is a uniform
categorical moduli space if and only if every base change along a flat morphism
from an affine scheme is a categorical moduli space. -/
theorem isUniformCategoricalModuliSpace_iff_forall_affine
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (f : X ⟶ Y.toGroupoids) :
    IsUniformCategoricalModuliSpace f ↔
      ∀ (Y' : Over S) [IsAffine Y'.left]
        (g : AlgebraicSpace.ofOver Y' ⟶ Y) [AlgebraicSpace.Flat g],
        IsCategoricalModuliSpace (pullbackSnd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
