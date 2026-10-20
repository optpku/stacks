/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.13.1: if `X` is a Noetherian algebraic space over a scheme `S` and `F` is a
coherent `𝒪_X`-module, then every ascending `ℕ`-indexed chain of quasi-coherent submodules
of `F` is eventually constant. -/
@[stacks 07UJ] #check (
  AlgebraicGeometry.AlgebraicSpace.Modules.quasiCoherentSubobject_monotone_stabilizes :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsNoetherian X]
      (F : X.Modules) [F.IsCoherent]
      (f : ℕ →o Subobject F)
      (_ : ∀ n : ℕ, (((f n : Subobject F) : X.Modules)).IsQuasicoherent),
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m)
