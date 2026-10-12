/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Biderivation

@[expose] public section

universe u v w

#check (Biderivation : ∀ (A : Type u) (B : Type v) (M : Type w),
  [CommRing A] → [CommRing B] → [Algebra A B] →
  [AddCommGroup M] → [Module A M] → [Module B M] → [Module Bᵐᵒᵖ M] →
  [IsScalarTower A B M] → [IsScalarTower A Bᵐᵒᵖ M] →
  [SMulCommClass B Bᵐᵒᵖ M] → Type (max v w))
