/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.Epi
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.LeftTensor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-exact symmetric-power sequences in `ModuleCat`

The canonical short complex is data. Exactness and epimorphicity of its final map are exposed as
separate facts, with a conjunction only as a convenient right-exactness bridge.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

/-- The two morphisms in the symmetric-power sequence associated to `S` compose to zero. -/
theorem sequenceCompEqZero (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    leftTensorMap S.f n ≫ map S.g (n + 1) = 0 := sorry

/-- The canonical symmetric-power short complex in degree `n + 1`. -/
@[stacks 00DO "symmetric-power sequence in ModuleCat"]
noncomputable def sequence (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (leftTensorMap S.f n) (map S.g (n + 1))
    (sequenceCompEqZero S n)

/-- An exact pair ending in an epimorphism induces an exact symmetric-power pair. -/
@[stacks 00DO "exact symmetric-power sequence in ModuleCat"]
theorem sequence_exact (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ)
    (hS : S.Exact) [Epi S.g] :
    (sequence S n).Exact := sorry

/-- The final morphism in the symmetric-power sequence is epimorphic whenever `S.g` is. -/
instance sequence_epi (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ) [Epi S.g] :
    Epi (sequence S n).g := sorry

/-- The symmetric-power sequence associated to an exact pair ending in an epimorphism is right
exact. -/
@[stacks 00DO "right-exact symmetric-power sequence in ModuleCat"]
theorem sequence_exact_and_epi (S : ShortComplex (ModuleCat.{u} R)) (n : ℕ)
    (hS : S.Exact) [Epi S.g] :
    (sequence S n).Exact ∧ Epi (sequence S n).g := sorry

end ModuleCat.symmetricPower
