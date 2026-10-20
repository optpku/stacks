/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids hiding diagonal
open FiberedCategoryOver.Groupoids.Hom (diagonal)
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 102.3.6: The diagonal of a morphism of categories fibred in groupoids
is limit preserving if and only if the comparison along every directed affine
inverse limit is fully faithful. -/
@[stacks 0CMW]
#check (AlgebraicGeometry.Groupoids.Hom.diagonal.limitPreserving_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y),
    LimitPreserving (diagonal.{u + 1, u, u + 1} p) ↔ FullyFaithfulComparison p)

#check (AlgebraicGeometry.Groupoids.Hom.diagonal.limitPreserving :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y) [LimitPreserving p],
    LimitPreserving (diagonal.{u + 1, u, u + 1} p))
