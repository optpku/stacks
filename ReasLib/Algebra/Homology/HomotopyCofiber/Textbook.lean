/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Textbook coordinates for a mapping cone

This file records the block-matrix presentation of the mapping-cone differential after swapping
mathlib's canonical biproduct order into the textbook order.

@stack 0627
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace HomologicalComplex.homotopyCofiber.Textbook

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
variable {A B : ChainComplex V ℤ} (f : A ⟶ B)

/-- The degree `n` term of the mapping cone, in the textbook order
`B.X n ⊞ A.X (n - 1)`. -/
@[stacks 0627 "textbook degreewise coordinates for a mapping cone"]
def xIso (n : ℤ) :
    (homotopyCofiber f).X n ≅ B.X n ⊞ A.X (n - 1) :=
  XIsoBiprod f n (n - 1) (ComplexShape.down_mk n (n - 1) (sub_add_cancel n 1)) ≪≫
    biprod.braiding (A.X (n - 1)) (B.X n)

/-- Equation 15.28.6.1: in textbook coordinates, the differential of the mapping cone of
`f : A ⟶ B` is the block matrix `(d_B,n  f_{n-1}; 0  -d_A,n-1)`. -/
@[stacks 0627 "mapping-cone differential in textbook coordinates"]
theorem d_eq_ofComponents (n : ℤ) :
    (xIso f n).inv ≫ (homotopyCofiber f).d n (n - 1) ≫ (xIso f (n - 1)).hom =
      Biprod.ofComponents (B.d n (n - 1)) 0 (f.f (n - 1))
        (-A.d (n - 1) ((n - 1) - 1)) := sorry

end HomologicalComplex.homotopyCofiber.Textbook
