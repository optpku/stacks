/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.TensorProduct

/-! Compatibility check for the residue algebra map of complete local algebras. -/

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CompleteLocalAlgCat.residueFieldHom :
  ∀ (R : CompleteLocalAlgCat Λ k), R.carrier →ₐ[Λ] k)
