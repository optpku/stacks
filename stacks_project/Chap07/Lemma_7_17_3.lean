/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf.Representable
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.3

The quasi-compactness comparison for sheafified representables is owned by
ReasLib; this Chapter 7 entry preserves the source-facing recall.
-/

@[expose] public section

/- Lemma 7.17.3 (0D06): `U` is quasi-compact in a Grothendieck site exactly
when `J.sheafifiedRepresentable U` is quasi-compact in the sheaf category. -/
@[stacks 0D06] #check @CategoryTheory.GrothendieckTopology.QuasiCompactObject.sheafifiedRepresentable_iff
