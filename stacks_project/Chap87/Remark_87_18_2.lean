/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalScheme.IdealSystem

/-!
# Remark 87.18.2

Every quasi-compact and quasi-separated EGA formal scheme has a fundamental
system of ideals of definition.
-/

@[expose] public section

universe u

noncomputable section

/- Remark 87.18.2: every quasi-compact and quasi-separated formal scheme has a
fundamental system of ideals of definition. This is the translation of
Lemma 87.18.1 into the language of EGA formal schemes, using Remark 87.13.4. -/
@[stacks 0AJF] #check (AlgebraicGeometry.FormalScheme.exists_fundamentalSystem :
  ∀ (X : AlgebraicGeometry.FormalScheme.{u})
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier],
    Nonempty (AlgebraicGeometry.FormalScheme.FundamentalSystem X))
