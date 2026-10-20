/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Koszul
public import ReasLib.RingTheory.Sequence.Koszul.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication in Koszul complexes of module presheaves

The objectwise Koszul differential is compatible with the fixed-degree exterior product.  This
is the topology-independent presheaf bridge used by the corresponding sheaf statement.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace PresheafOfModules.Koszul

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The Koszul differential on a module presheaf satisfies the graded Leibniz rule in two
positive degrees. -/
@[stacks 062K "presheaf graded Leibniz rule"]
theorem differential_mul
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n m : ℕ) :
    ExteriorPower.mulHom O F (n + 1) (m + 1) ≫
        eqToHom
          (congrArg (ExteriorPower.presheaf O F)
            (Nat.succ_add n (m + 1))) ≫
        differential O phi (n + (m + 1)) =
      (differential O phi n ▷ ExteriorPower.presheaf O F (m + 1)) ≫
          ExteriorPower.mulHom O F n (m + 1) +
        ((-1 : ℤ) ^ (n + 1)) •
          ((ExteriorPower.presheaf O F (n + 1) ◁ differential O phi m) ≫
            ExteriorPower.mulHom O F (n + 1) m ≫
            eqToHom
              (congrArg (ExteriorPower.presheaf O F)
                ((Nat.succ_add n m).trans (Nat.add_succ n m).symm))) := sorry

/-- The presheaf Koszul differential commutes with exterior multiplication by a degree-zero
element on the right. -/
@[stacks 062K "presheaf right degree-zero Leibniz rule"]
theorem differential_mul_zero_right
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (n : ℕ) :
    ExteriorPower.mulHom O F (n + 1) 0 ≫
        eqToHom
          (congrArg (ExteriorPower.presheaf O F) (Nat.add_zero (n + 1))) ≫
        differential O phi n =
      (differential O phi n ▷ ExteriorPower.presheaf O F 0) ≫
        ExteriorPower.mulHom O F n 0 ≫
        eqToHom
          (congrArg (ExteriorPower.presheaf O F) (Nat.add_zero n)) := sorry

/-- The presheaf Koszul differential commutes with exterior multiplication by a degree-zero
element on the left. -/
@[stacks 062K "presheaf left degree-zero Leibniz rule"]
theorem differential_zero_mul
    {F : PresheafOfModules.{w} (RingPresheaf O)}
    (phi : F ⟶ PresheafOfModules.unit (RingPresheaf O)) (m : ℕ) :
    ExteriorPower.mulHom O F 0 (m + 1) ≫
        eqToHom
          (congrArg (ExteriorPower.presheaf O F) (Nat.zero_add (m + 1))) ≫
        differential O phi m =
      (ExteriorPower.presheaf O F 0 ◁ differential O phi m) ≫
        ExteriorPower.mulHom O F 0 m ≫
        eqToHom
          (congrArg (ExteriorPower.presheaf O F) (Nat.zero_add m)) := sorry

end PresheafOfModules.Koszul
