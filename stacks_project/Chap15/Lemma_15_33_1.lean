/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Generators.KoszulRegular

/-!
# Lemma 15.33.1

@stack 07CZ
-/

@[expose] public section

/- Lemma 15.33.1, tag `07CZ`: Koszul-regularity of the kernel of a finite
polynomial presentation is independent of the chosen presentation. The reusable owner lives on
`Algebra.Generators`, not in this source-facing chapter. -/
@[stacks 07CZ "Koszul-regular presentation kernels are presentation-independent"]
#check @Algebra.Generators.ker_isKoszulRegularIdeal_iff

#check @Algebra.Generators.ker_isKoszulRegularIdeal_of_presentation
