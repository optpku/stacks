/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Locally finite graded modules

A ℤ-indexed family of submodules is locally finite when every piece is a finite module.
This property does not require a direct-sum decomposition of the ambient module.
-/

@[expose] public section

universe u v

namespace GradedModule

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/-- A family of submodules is locally finite when every degree piece is a finite module. -/
@[mk_iff]
class LocallyFinite (ℳ : ℤ → Submodule A M) : Prop where
  /-- Each degree piece is a finite `A`-module. -/
  finite_piece (n : ℤ) : Module.Finite A (ℳ n)

variable (ℳ : ℤ → Submodule A M)

/-- Every piece of a locally finite family is a finite module. -/
instance instFinitePiece [LocallyFinite ℳ] (n : ℤ) : Module.Finite A (ℳ n) :=
  LocallyFinite.finite_piece n

/-- The family consisting of zero submodules is locally finite. -/
instance instLocallyFiniteBot : LocallyFinite (fun _ : ℤ ↦ (⊥ : Submodule A M)) :=
  ⟨fun _ ↦ inferInstance⟩

end GradedModule
