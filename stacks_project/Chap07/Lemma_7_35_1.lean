/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.OverFiber
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.35.1

The coefficient-general point-localization fiber comparison is owned by ReasLib; this Chapter 7
entry is the source-facing recall.
-/

@[expose] public section

/- Lemma 7.35.1 (04H2): if `x : p.fiber.obj U`, then the fiber at the localized point `p.over x`
of a sheaf restricted to `C / U` is canonically the fiber at `p`. -/
@[stacks 04H2] #check @CategoryTheory.GrothendieckTopology.Point.OverFiber.sheafIso

@[stacks 04H2] #check @CategoryTheory.GrothendieckTopology.Point.OverFiber.sheafObjIso
