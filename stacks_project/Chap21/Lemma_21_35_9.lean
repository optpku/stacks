/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Duality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.9

The degree-zero comparison is owned by the ringed-site derived duality leaf in ReasLib.  This
chapter file keeps only source-labelled recall checks, so later chapters can import the shared
owner directly.
-/

/- Lemma 21.35.9 (08JD): the canonical map from degree-zero global sections to derived morphisms. -/
@[stacks 08JD "derived degree-zero dual comparison"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationH0ToHom

@[stacks 08JD "derived degree-zero dual comparison specification"] #check
  @SheafOfModules.RingedSite.curry'_ringedSiteDerivedEvaluationH0ToHom

@[stacks 08JD "derived degree-zero dual comparison naturality"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationH0ToHom_natural

@[stacks 08JD "additivity of the derived degree-zero dual comparison"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationH0ToHom_add

@[stacks 08JD "additive derived degree-zero dual comparison"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationH0ToHomAddMonoidHom

@[stacks 08JD "AddCommGrp-valued derived degree-zero dual comparison"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationH0ToHomAddCommGrpHom
