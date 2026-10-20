/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 29.4.3

Exceptional inverse image for quasicoherent modules along a closed immersion.

@stack 01R0
-/

@[expose] public section

open CategoryTheory

universe u

variable {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
  [AlgebraicGeometry.IsClosedImmersion i]

/- Lemma 29.4.3: for a closed immersion, pushforward on quasicoherent modules admits
an exceptional inverse image as a right adjoint. -/
@[stacks 01R0] #check
  (AlgebraicGeometry.Scheme.QCoh.pushforwardShriekAdjunction i :
    AlgebraicGeometry.Scheme.QCoh.pushforward i ⊣ AlgebraicGeometry.Scheme.QCoh.shriek i)
