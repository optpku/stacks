/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Localization.Descent
import StacksCheckRecall

@[expose] public section

/- Lemma 16.8.3: the localized smooth-factorisation descent and its
elementary-standard denominator are owned by `AlgHom.Localization.Descent`. -/
@[stacks 07F4]
#check @AlgHom.Localization.Descent.nonempty

#check @AlgHom.Localization.Descent
#check @AlgHom.Localization.Descent.of
#check @AlgHom.Localization.Descent.spec
