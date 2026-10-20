/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.IsoClassSheaf
import StacksCheckRecall

/-!
# Sheafification of isomorphism classes of a gerbe

If an algebraic stack is a gerbe, the fppf sheafification of its presheaf of
fiberwise isomorphism classes is identified with an algebraic space, and the
stack is a gerbe over that sheafification via its presentation over the space.
The identification is the canonical comparison associated to the presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.28.2: the iso-class sheafification of a gerbe algebraic stack is
identified with an algebraic-space base over which the stack is a gerbe. -/
@[stacks 06QD] #check
  (AlgebraicGeometry.AlgebraicStack.exists_isoClassSheafComparison_isIso :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsGerbe X],
      ∃ (Y : AlgebraicSpace S) (π : X ⟶ Y.toGroupoids),
        AlgebraicStack.Gerbe π ∧ IsIso (AlgebraicStack.isoClassSheafComparison π))

#check (AlgebraicGeometry.AlgebraicStack.isoClassSheafComparison_isIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : AlgebraicSpace S} (π : X ⟶ Y.toGroupoids) [AlgebraicStack.Gerbe π],
    IsIso (AlgebraicStack.isoClassSheafComparison π))
