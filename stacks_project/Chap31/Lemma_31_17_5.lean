/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.QuasiAffine
import StacksCheckRecall

/-!
# Lemma 31.17.5

Descent of quasi-affineness along a finite morphism admitting a norm.

@stack 0BD1
-/

@[expose] public section

universe u

/- Lemma 31.17.5: let `π : X ⟶ Y` be a finite morphism of schemes. If `X` is quasi-affine
and `π` admits a norm of degree `d`, then `Y` is quasi-affine. -/
@[stacks 0BD1] #check (
  AlgebraicGeometry.Scheme.IsQuasiAffine.target_of_finiteMorphismNorm :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y) [AlgebraicGeometry.IsFinite π]
      (d : ℕ) (hX : X.IsQuasiAffine)
      (hnorm : ∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm π,
        AlgebraicGeometry.Scheme.IsFiniteMorphismNorm π d N),
      Y.IsQuasiAffine)
