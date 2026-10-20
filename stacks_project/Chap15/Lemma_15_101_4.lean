/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.IdealPower.Quotient.Iso.Noetherian

@[expose] public section

/-!
# Lemma 15.101.4: Hom over ideal-power quotients

@stack 09BB
-/

open CategoryTheory
open CategoryTheory.Limits
open Ideal.PowerQuotient

/- Lemma 15.101.4 (09BB): let `R` be Noetherian, let `I : Ideal R`, and let
`M` and `N` be finite `R`-modules.  The Hom and isomorphism systems of the
positive ideal-power quotients are Mittag-Leffler; the quotient-Hom comparison
has uniformly annihilated kernel and cokernel; and their limits recover the
corresponding objects over the `I`-adic completions.

The sequential facade uses stage `n` for the textbook exponent `n + 1`.
Reusable stages, transitions, comparisons, and completion maps are owned by
`ReasLib`; this chapter boundary is intentionally API-only. -/

/- Lemma 15.101.4 (1): the Hom system is Mittag-Leffler. -/
@[stacks 09BB "Mittag-Leffler property for Hom over ideal-power quotients"]
#check @Hom.quotientSystem_isMittagLeffler

/- The canonical `Hom_R(M, N / I ^ (n + 1) N)` model is the computationally smaller
presentation of the same system. -/
#check @Hom.system_isMittagLeffler

/- Lemma 15.101.4 (1): the system of quotient-stage linear equivalences is
Mittag-Leffler. -/
@[stacks 09BB "Mittag-Leffler property for isomorphisms over ideal-power quotients"]
#check @Iso.system_isMittagLeffler

/- Lemma 15.101.4 (2): one power of `I` annihilates every kernel and
cokernel of the canonical quotient-Hom comparison. -/
@[stacks 09BB "uniform annihilation for the quotient Hom comparison"]
#check @Hom.exists_quotientComparison_kernel_cokernel_annihilation

/- The canonical-model annihilation theorem is available as the computational bridge. -/
#check @Hom.exists_comparison_kernel_cokernel_annihilation

/- Positive-exponent companions are available when a downstream argument needs
the witness normalized away from exponent zero. -/
#check @Hom.exists_quotientComparison_kernel_cokernel_annihilation_pos
#check @Hom.exists_comparison_kernel_cokernel_annihilation_pos

/- Lemma 15.101.4 (3): the canonical completion-to-limit map for Hom is an
isomorphism. -/
@[stacks 09BB "limit of Hom over ideal-power quotients"]
#check @Hom.quotientLimitComparison_isIso

/- The smaller canonical model and its comparison remain directly reusable. -/
#check @Hom.limitComparison_isIso

/- The concrete map and its projection formula remain available independently
of the Noetherian and finiteness hypotheses. -/
#check @Hom.limitComparison
#check @Hom.limitComparison_comp_π
#check @Hom.quotientLimitComparison
#check @Hom.quotientLimitComparison_comp_π
#check @Hom.limit_isIsomorphic_adicCompletion
#check @Hom.quotientLimit_isIsomorphic_adicCompletion

/- Lemma 15.101.4 (3): completed Hom agrees with Hom between completions. -/
@[stacks 09BB "completed Hom comparison"]
#check @Hom.completedHomComparison
#check @Hom.completedHomComparison_isIso
#check @Hom.eval_completedEvaluation_succ
#check @Hom.completedEvaluation_of
#check @Hom.completedHom_isIsomorphic_completedLinearMap

/- Lemma 15.101.4 (4): compatible quotient-stage equivalences are identified
with linear equivalences between the completed modules. -/
@[stacks 09BB "limit of isomorphisms over ideal-power quotients"]
#check @Iso.limitComparison_bijective

#check @Iso.limitComparison
#check @Iso.limit_isIsomorphic_completionEquiv

/- The source-facing quotient-domain Hom and the smaller canonical model are
connected by a reusable equivalence, rather than identified only in prose. -/
#check @Hom.exactStage
#check @Hom.exactQuotientStage
#check @Hom.exactStageEquiv
#check @Hom.exactRestrictDomain_apply
#check @Hom.exactLiftDomain_mk
#check @Hom.exactComparison
#check @Hom.exactQuotientComparison
#check @Hom.quotientStage
#check @Hom.quotientStageEquiv
#check @Hom.quotientStep
#check @Hom.quotientSystem
#check @Hom.quotientSystemIso
#check @Hom.stage
#check @Hom.step
#check @Hom.system
#check @Hom.comparison
#check @Hom.comparisonNatTrans

/- The quotient-isomorphism tower exposes its reduction operation and concrete
completion maps separately for downstream use. -/
#check @Iso.stage
#check @Iso.reduce
#check @Iso.system
#check @Iso.completionMap
#check @Iso.completionInv
