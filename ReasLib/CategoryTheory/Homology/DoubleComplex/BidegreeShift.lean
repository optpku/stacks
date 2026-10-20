/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bidegree shifts of double complexes

This file combines mathlib's shifts in the two directions of a cohomological double complex.
It exposes both the canonical comparison from the total of a shifted double complex to the
shifted total and the inverse-facing view used by component calculations.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Shift a cohomological double complex by `a` in the first direction and by `b` in the
second direction. -/
@[stacks 0FLG]
abbrev bidegreeShift (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (a b : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor₁ C a).obj ((shiftFunctor₂ C b).obj K)

variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (a b : ℤ)
variable [K.HasTotal (up ℤ)]

namespace BidegreeShift

/-- The canonical comparison from the total complex of a bidegree shift to the total complex
shifted by the sum of the two degrees. -/
@[stacks 0FLG]
noncomputable def totalIso :
    (K.bidegreeShift a b).total (up ℤ) ≅ (K.total (up ℤ))⟦a + b⟧ :=
  (((shiftFunctor₂ C b).obj K).totalShift₁Iso a) ≪≫
    (shiftFunctor _ a).mapIso (K.totalShift₂Iso b) ≪≫
    ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app (K.total (up ℤ))).symm

/-- If `(p,q)` has total degree `n + (a + b)`, then `(p-a,q-b)` has total degree `n`. -/
theorem index_eq
    (n p q : ℤ) (h : p + q = n + (a + b)) :
    (p - a) + (q - b) = n := sorry

/-- On an antidiagonal summand, the inverse-facing bidegree-shift comparison contributes the
Koszul sign `(-1)^(p*b)` and includes the shifted bidegree `(p-a,q-b)`. -/
@[stacks 0FLG, reassoc]
theorem ι_totalIso_symm_hom_f
    (n p q : ℤ) (h : p + q = n + (a + b)) :
    K.ιTotal (up ℤ) p q (n + (a + b)) h ≫
        (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) (a + b)
          n (n + (a + b)) rfl).inv ≫
        (totalIso K a b).symm.hom.f n =
      (p * b).negOnePow •
        ((K.shiftFunctor₂XXIso p (q - b) b q (Int.sub_add_cancel q b).symm).inv ≫
          (((shiftFunctor₂ C b).obj K).shiftFunctor₁XXIso (p - a) a p
            (Int.sub_add_cancel p a).symm (q - b)).inv ≫
            (K.bidegreeShift a b).ιTotal (up ℤ) (p - a) (q - b) n
              (index_eq (a := a) (b := b) n p q h)) := sorry

end BidegreeShift

end HomologicalComplex₂
