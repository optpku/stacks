/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Basis.LocalRing
import StacksCheckRecall

/-!
# Lifting a basis from the residue field

@stack 051F
-/

@[expose] public section

open IsLocalRing

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
variable {A : Type w}

/- Lemma 10.101.1: for a flat module over a local ring with nilpotent maximal ideal, the images
of a family in the residue-field quotient form a basis exactly when the family forms a basis. -/
@[stacks 051F]
#check (Module.Basis.LocalRing.basis_mod_maximalIdeal_iff (R := R) (M := M) (A := A) :
  IsNilpotent (maximalIdeal R) → ∀ (x : A → M),
    (∃ bbar : Module.Basis A (R ⧸ maximalIdeal R)
        (M ⧸ (maximalIdeal R • (⊤ : Submodule R M))),
      ∀ a, bbar a = Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R M)) (x a)) ↔
      ∃ b : Module.Basis A R M, ∀ a, b a = x a)

end
