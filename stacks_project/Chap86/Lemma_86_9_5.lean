/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing.Existence
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

/- Lemma 86.9.5: let `S` be a scheme. Let `X ⟶ Y` be a proper, flat morphism of
algebraic spaces which is of finite presentation. There exists a relative dualizing
complex `(ω, τ)`. -/
@[stacks 0E61] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.nonempty :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [Proper f] → [Flat f] → [FinitePresentation f] → Nonempty (RelativeDualizingComplex f))
