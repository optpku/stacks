/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion
import StacksCheckRecall

/-!
@stack 091R

Lemma 15.92.3 is a source-facing bridge to the shared comparison between ordinary adic
completeness and derived completeness.  Its reusable objects, multiplication tower, and both
directions are owned by `ReasLib`.
-/

@[expose] public section

/- Lemma 15.92.3 (Stacks `091R`): the reusable pointwise vanishing predicate for `T(M, f)`. -/
@[stacks 091R "pointwise localization-away vanishing"]
#check @ModuleCat.moduleLocalizationAwayTVanishing

/- Lemma 15.92.3 (Stacks `091R`): the concrete inverse system with transition `f • 𝟙 M`. -/
@[stacks 091R "the explicit module multiplication tower"]
#check @ModuleCat.localizationAwayModuleTower

/- Lemma 15.92.3 (Stacks `091R`): the shared finitely-generated generatorwise completion API. -/
@[stacks 091R "the generatorwise adic-completion criterion"]
#check @AdicCompletion.surjective_of_span_eq_of_generatorwise

/- Lemma 15.92.3 (Stacks `091R`) (1): adic completeness implies derived completeness. -/
@[stacks 091R "adic completeness implies derived completeness"]
#check @ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete

/- Lemma 15.92.3 (Stacks `091R`) (2): finite-generation plus derived completeness gives a
surjective ordinary adic-completion map. -/
@[stacks 091R "derived completeness implies surjective adic completion"]
#check @ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo
