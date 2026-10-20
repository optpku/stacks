/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Functor

/- Lemma 18.15.2 (04DB) (1): exactness follows when a compared type-valued direct
image preserves epimorphisms. -/
@[stacks 04DB "underlying epimorphisms"]
#check @AbelianPushforward.Comparison.exact_of_epi

/- Lemma 18.15.2 (04DB) (2): additive direct image is exact if it preserves epimorphisms. -/
@[stacks 04DB "abelian epimorphisms"]
#check @AbelianPushforward.exact_of_preservesEpimorphisms

/- Lemma 18.15.2 (04DB) (3): preserving coequalizers on the compared type-valued direct image is
sufficient. -/
@[stacks 04DB "underlying coequalizers"]
#check @AbelianPushforward.Comparison.exact_of_coequalizers

/- Lemma 18.15.2 (04DB) (4): preserving pushouts on the compared type-valued direct image is
sufficient. -/
@[stacks 04DB "underlying pushouts"]
#check @AbelianPushforward.Comparison.exact_of_pushouts
