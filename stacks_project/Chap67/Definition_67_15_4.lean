/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 67.15.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `F` be a finite type quasi-coherent `𝒪_X`-module. The scheme-theoretic support
of `F` is the closed subspace `Z ⊂ X` constructed in Lemma 67.15.3. -/
@[stacks 07U1] #check (AlgebraicGeometry.AlgebraicSpace.Modules.schemeTheoreticSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType], ClosedSubspace X)
