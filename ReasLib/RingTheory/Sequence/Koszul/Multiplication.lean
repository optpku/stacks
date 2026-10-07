module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Multiplication
public import ReasLib.RingTheory.Sequence.Koszul.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication in Koszul complexes

This leaf records the fixed-degree graded Leibniz rule for contraction by a linear form.  It is
the algebraic owner used by presheaf and sheaf Koszul complexes; no differential graded algebra
packaging or reindexing convention is imposed here.
@stack 0622
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

variable {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E]

/-- The Koszul differential is a graded derivation for exterior multiplication in two positive
degrees.  The first input has degree `n + 1`, so its Leibniz sign is `(-1)^(n + 1)`. -/
@[stacks 0622 "(2), Koszul differential is a derivation", stacks 062K "graded Leibniz rule"]
theorem koszulDifferential_mul (phi : E →ₗ[R] R) (n m : ℕ) :
    ModuleCat.exteriorPower.mul (ModuleCat.of R E) (n + 1) (m + 1) ≫
        eqToHom
          (congrArg (fun d ↦ (ModuleCat.of R E).exteriorPower d)
            (Nat.succ_add n (m + 1))) ≫
        koszulDifferential phi (n + (m + 1)) =
      (koszulDifferential phi n ▷ (ModuleCat.of R E).exteriorPower (m + 1)) ≫
          ModuleCat.exteriorPower.mul (ModuleCat.of R E) n (m + 1) +
        ((-1 : ℤ) ^ (n + 1)) •
          (((ModuleCat.of R E).exteriorPower (n + 1) ◁ koszulDifferential phi m) ≫
            ModuleCat.exteriorPower.mul (ModuleCat.of R E) (n + 1) m ≫
            eqToHom
              (congrArg (fun d ↦ (ModuleCat.of R E).exteriorPower d)
                ((Nat.succ_add n m).trans (Nat.add_succ n m).symm))) := sorry

/-- Multiplication by a degree-zero exterior element on the right commutes with the Koszul
differential. -/
@[stacks 062K "right degree-zero Leibniz rule"]
theorem koszulDifferential_mul_zero_right (phi : E →ₗ[R] R) (n : ℕ) :
    ModuleCat.exteriorPower.mul (ModuleCat.of R E) (n + 1) 0 ≫
        eqToHom
          (congrArg (fun d ↦ (ModuleCat.of R E).exteriorPower d)
            (Nat.add_zero (n + 1))) ≫
        koszulDifferential phi n =
      (koszulDifferential phi n ▷ (ModuleCat.of R E).exteriorPower 0) ≫
        ModuleCat.exteriorPower.mul (ModuleCat.of R E) n 0 ≫
        eqToHom
          (congrArg (fun d ↦ (ModuleCat.of R E).exteriorPower d)
            (Nat.add_zero n)) := sorry

/-- Multiplication by a degree-zero exterior element on the left commutes with the Koszul
differential. -/
@[stacks 062K "left degree-zero Leibniz rule"]
theorem koszulDifferential_zero_mul (phi : E →ₗ[R] R) (m : ℕ) :
    ModuleCat.exteriorPower.mul (ModuleCat.of R E) 0 (m + 1) ≫
        eqToHom
          (congrArg (fun d ↦ (ModuleCat.of R E).exteriorPower d)
            (Nat.zero_add (m + 1))) ≫
        koszulDifferential phi m =
      ((ModuleCat.of R E).exteriorPower 0 ◁ koszulDifferential phi m) ≫
        ModuleCat.exteriorPower.mul (ModuleCat.of R E) 0 m ≫
        eqToHom
          (congrArg (fun d ↦ (ModuleCat.of R E).exteriorPower d)
            (Nat.zero_add m)) := sorry
