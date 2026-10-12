/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Over.LeftKanExtension
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
# Remark 7.25.10

The generic left-Kan-extension calculation for `Over.forget U` belongs to the
functor-level ReasLib leaf, independently of any site topology.
-/

/- Remark 7.25.10 (0494): the presheaf-level localization lower shriek is left
Kan extension along `(Over.forget U).op`; objectwise it is the coproduct over
maps to `U`, and it preserves fibre products and equalizers. -/
@[stacks 0494] #check @CategoryTheory.Over.Forget.LeftKanExtension.objIsoSigma

@[stacks 0494] #check @CategoryTheory.Over.Forget.LeftKanExtension.preservesFiniteConnectedLimits

@[stacks 0494] #check @CategoryTheory.Over.Forget.LeftKanExtension.preservesPullbacks

@[stacks 0494] #check @CategoryTheory.Over.Forget.LeftKanExtension.preservesEqualizers
