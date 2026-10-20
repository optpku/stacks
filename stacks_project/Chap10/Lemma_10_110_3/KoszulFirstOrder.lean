/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_110_3.LocalKoszul
import StacksCheckRecall

@[expose] public section

/-!
First-order Koszul support for Lemma 10.110.3.
@stack 00OA
-/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: the first-order Koszul kernel for a cotangent-basis lift is
contained in the maximal-ideal multiple of the source term. -/
lemma localKoszulDifferential_firstOrder_kernel_of_cotangentBasis
    {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R))
    (x : Fin n → maximalIdeal R)
    (hx : ∀ j, (maximalIdeal R).toCotangent (x j) = b j)
    {i : ℕ} (hi : i < n)
    {z : (localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X (i + 1)}
    (hz :
      ((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).d (i + 1) i).hom z ∈
        (maximalIdeal R) ^ 2 •
          (⊤ : Submodule R
            ((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X i))) :
    z ∈ maximalIdeal R •
      (⊤ : Submodule R
        ((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X (i + 1))) := sorry

end

@[stacks 00OA "first-order Koszul kernel"]
#check @localKoszulDifferential_firstOrder_kernel_of_cotangentBasis
