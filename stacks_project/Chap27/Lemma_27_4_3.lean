/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Representability

/-!
# Lemma 27.4.3 compatibility entry point

Global representability of the relative-spectrum functor is owned by ReasLib.
-/

@[expose] public section

universe u

/- Lemma 27.4.3: global representability of the relative-spectrum functor. -/
@[stacks 01LU] #check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctor.instIsRepresentable :
    {S : AlgebraicGeometry.Scheme.{u}} → (A : S.QcAlgebraUnder) →
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentable)
