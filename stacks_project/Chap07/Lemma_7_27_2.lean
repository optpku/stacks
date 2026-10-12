/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Localization.Basic
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Lemma 7.27.2

Localization direct image is the `Over.forget U ⊣ Over.star U` specialization of the generic
continuous-right-adjoint direct-image comparison.
-/

@[expose] public section

/- Lemma 7.27.2 (00Y2): the localization direct image and its source-facing section formula
are supplied by the canonical `Over.forget U ⊣ Over.star U` adjunction and the generic
continuous-right-adjoint comparison. -/
@[stacks 03CE] #check @CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso

/- The localization adjunction identifies the right-adjoint slice object used in the section
formula. -/
#check @CategoryTheory.Over.forgetAdjStar
