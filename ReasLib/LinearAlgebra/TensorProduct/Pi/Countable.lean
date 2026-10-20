/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Countable.Defs
public import ReasLib.LinearAlgebra.TensorProduct.Pi.FinitePresentation

@[expose] public section

universe u v

namespace Module.Finite

/-- A countable module is finitely generated if and only if tensoring the
countable scalar product maps surjectively onto the product of the module. -/
theorem iff_piScalarRightHom_nat_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] [Countable M] :
    Module.Finite R M ↔
      Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ) := sorry

end Module.Finite

namespace Module.FinitePresentation

/-- A countable module over a countable ring is finitely presented if and only if
the canonical comparison from tensoring the countable scalar product to the
countable product of the module is bijective. -/
@[stacks 0ALA]
theorem iff_piScalarRightHom_nat_bijective {R : Type u} [CommRing R] [Countable R]
    {M : Type v} [AddCommGroup M] [Module R M] [Countable M] :
    Module.FinitePresentation R M ↔
      Function.Bijective (TensorProduct.piScalarRightHom R R M ℕ) := sorry

end Module.FinitePresentation
