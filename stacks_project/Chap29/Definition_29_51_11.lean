/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
import StacksCheckRecall

@[expose] public section

/- Definition 29.51.11: For integral schemes `X'` and `X`, a morphism `f : X' ⟶ X`
is a modification exactly when it is birational and proper. -/
@[stacks 0AAZ] #check
  (AlgebraicGeometry.isModification_iff :
    ∀ {X' X : AlgebraicGeometry.Scheme} (f : X' ⟶ X)
      [AlgebraicGeometry.IsIntegral X'] [AlgebraicGeometry.IsIntegral X],
      AlgebraicGeometry.IsModification f ↔
        AlgebraicGeometry.IsBirational f ∧ AlgebraicGeometry.IsProper f)
