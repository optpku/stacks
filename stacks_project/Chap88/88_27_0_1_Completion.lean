/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor

/-!
# Completion along a closed subset

Compatibility names for completion and the canonical restricted completion functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The open complement of a closed subset of the points of an algebraic space. -/
abbrev openComplement {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    Opens (Points X) := T.compl

namespace completionAlong

/-- The completion of a locally Noetherian algebraic space along a closed subset
is a formal algebraic space. -/
def instIsFormalAlgebraicSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T) :=
  inferInstance

/-- The completion of a locally Noetherian algebraic space along a closed subset
is a locally Noetherian formal algebraic space. -/
def instIsLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlong X T) :=
  inferInstance

/-- The completion functor sending a morphism to its canonical completion map. -/
abbrev functor {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)) : Source X T ⥤ Target X T :=
  completionFunctor X T

end completionAlong

end AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.functor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [AlgebraicSpace.IsLocallyNoetherian X]
    (T : Closeds (AlgebraicSpace.Points X)),
    AlgebraicSpace.completionAlong.Source X T ⥤ AlgebraicSpace.completionAlong.Target X T)
