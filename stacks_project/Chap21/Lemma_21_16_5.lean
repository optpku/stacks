/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.16.5

The stagewise injective enlargement is owned by the reusable compatible-stage-family API.  This
chapter entry keeps only the source-facing Stacks recall.
-/

/- Lemma 21.16.5 (0EXZ): every compatible abelian-sheaf family admits a stagewise monomorphic map
to a family of injective sheaves. -/
@[stacks 0EXZ "stagewise injective enlargement"]
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.exists_mono_to_injective

#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.IsStagewiseInjective
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Hom.IsStagewiseMono
