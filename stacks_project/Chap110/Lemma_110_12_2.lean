/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Pi.Countable

@[expose] public section

universe u v

variable {R : Type u} [CommRing R] [Countable R]
    {M : Type v} [AddCommGroup M] [Module R M] [Countable M]

/- Lemma 110.12.2: if `R` is a countable ring and `M` is a countable `R`-module,
then `M` is a finitely presented `R`-module if and only if the canonical map
`M ⊗[R] (ℕ → R) ⟶ (ℕ → M)` is an isomorphism. -/
@[stacks 0ALA] #check
  (Module.FinitePresentation.iff_piScalarRightHom_nat_bijective (R := R) (M := M) :
    Module.FinitePresentation R M ↔
      Function.Bijective (TensorProduct.piScalarRightHom R R M ℕ))
