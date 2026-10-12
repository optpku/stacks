/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.MittagLeffler.Presentation

@[expose] public section

/-!
# Mittag-Leffler directed presentations

Proposition 10.88.6 is provided by the reusable presentation API.

@stack 059E
-/

@[stacks 059E]
#check Module.MittagLeffler.Presentation.mittagLeffler_tfae

@[stacks 059E "stage-domination criterion"]
#check Module.MittagLeffler.Presentation.kernelFactorization_iff_stageDomination

@[stacks 059E "hom-Mittag-Leffler criterion"]
#check Module.MittagLeffler.Presentation.kernelFactorization_iff_homMittagLeffler

@[stacks 059E "tail-factorization criterion"]
#check CategoryTheory.Functor.HomMittagLeffler.iff_tailFactorization

@[stacks 059E "product criterion"]
#check CategoryTheory.Functor.HomMittagLeffler.iff_product
