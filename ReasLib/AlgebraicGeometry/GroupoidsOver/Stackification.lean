/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification.LocalEquivalence

/-!
# Stackification over the big fppf site with original-universe Hom types

Actual small local Hom codes retain the standard `GroupoidsOver S` universe.
The original fibred projection supplies its cleavage internally.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Stackification

variable {S : Scheme.{u}} {X : Type (u + 1)} [Category.{u} X]

/-- An fppf stackification in the original `GroupoidsOver S` universe. -/
@[stacks 02ZP "fppf stackification in the original Hom universe"]
structure Presentation (p : X ⥤ Over S) [Functor.IsFibered.InGroupoids p] where
  target : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)
  comparison : CartesianBasedFunctor p target.p
  isStackification : CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S) comparison

/-- The original fibredness supplies the cleavage; actual small Hom codes
and actual local descent witnesses supply the target and comparison. -/
@[stacks 02ZP "actual fppf stackification presentation"]
def presentation (p : X ⥤ Over S) [Functor.IsFibered.InGroupoids p] : Presentation p where
  target := smallTarget p (Functor.Cleavage.ofIsFibered p)
  comparison := smallComparison p (Functor.Cleavage.ofIsFibered p)
  isStackification := smallComparisonIsStackification p (Functor.Cleavage.ofIsFibered p)

end AlgebraicGeometry.GroupoidsOver.Stackification
