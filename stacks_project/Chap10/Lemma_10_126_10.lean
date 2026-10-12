/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.126.10

The reusable quotient-and-flatness localization criterion is owned by
`AlgHom.Localization.AtPrime`.  This file keeps the textbook hypotheses and
records their canonical owner and finite-presentation bridge under tag `087P`.

@stack 087P
-/

/- Lemma 10.126.10: let `R` be a ring, let `I` be an ideal of `R`, let
`f : S → S'` be a surjective `R`-algebra map, and let `q` be a prime ideal of `S` containing
`Ideal.map (algebraMap R S) I`.  If `S` is of finite type over `R`, `S'` is of finite presentation
over `R`, the induced quotient algebra map on the localizations at `q.primeCompl` modulo `I` is
bijective, and the localized target is flat over `R`, then there exists `g ∉ q` such that
`Localization.awayMapₐ f g` is bijective.  The generic owner is
`AlgHom.Localization.AtPrime.exists_notMem_awayMap_bijective_of_quotientMap_bijective`. -/
@[stacks 087P "source-facing quotient-and-flatness localization criterion"]
#check @AlgHom.Localization.AtPrime.exists_notMem_awayMap_bijective_of_quotientMap_bijective

@[stacks 087P "finite-presentation hypothesis bridge"]
#check @RingHom.FinitePresentation.of_algebra
