/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldCover.Etale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 101.21.4
A DM, locally Noetherian, reduced algebraic stack whose space of points is a
singleton admits a surjective étale morphism from the spectrum of a field.
-/
@[stacks 06N0] #check
  (AlgebraicGeometry.AlgebraicStack.existsSurjectiveEtaleSpecField_of_isDM :
    ∀ {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsDM Z]
      [IsLocallyNoetherian Z] [IsReduced Z] [Nonempty (Points Z)]
      [Subsingleton (Points Z)], existsSurjectiveEtaleSpecField Z)
