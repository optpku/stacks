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
# Lemma 21.35.9.1

This chapter entry is a recall facade.  The concrete dual, evaluation, and specification maps are
owned by `ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Duality`.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite

/- Lemma 21.35.9.1 (08JE): the derived closed-monoidal dual and evaluation maps. -/
@[stacks 08JE "derived closed-monoidal dual"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedDualObject

@[stacks 08JE "derived tensor/internal-Hom comparison"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationHom

@[stacks 08JE "derived tensor/internal-Hom comparison specification"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedEvaluationHom_uncurry

@[stacks 08JE "derived dual evaluation"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedDualEvaluation

@[stacks 08JE "derived dual evaluation specification"] #check
  @SheafOfModules.RingedSite.ringedSiteDerivedDualEvaluation_eq_braided_uncurry
