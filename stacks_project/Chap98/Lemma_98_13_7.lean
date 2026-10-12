/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.«98_13_2_1_Smooth»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness from the predeformation criterion

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces, satisfies (98.13.2.1), is limit preserving
on objects over `(Sch/S)_fppf`, and has a limit-preserving target, is smooth
when `S` is locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 98.13.7: if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces, satisfies (98.13.2.1), has
`X ⟶ (Sch/S)_fppf` limit preserving on objects, and has `Y` limit
preserving, then `f` is smooth. -/
@[stacks 07XX]
theorem Smooth.of_isSmoothOnPredeformations {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsSmoothOnPredeformations f]
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    [LimitPreserving Y] :
    Smooth f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
