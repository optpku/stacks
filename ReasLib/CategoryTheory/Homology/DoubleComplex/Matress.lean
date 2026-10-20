/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.CategoryTheory.Homology.DoubleComplex.BidegreeShift

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Matress

/-- TR3 sign for unsigned shifted triangle maps: normalized source and target
third arrows contribute (-1)^(-p) and (-1)^q, respectively. -/
def fillerSign (p q : ℤ) : ℤˣ := (p + q).negOnePow

/-- The two normalized triangle signs give precisely the filler sign. -/
theorem fillerSign_from_triangle_signs (p q : ℤ) :
    (-p).negOnePow * q.negOnePow = fillerSign p q := by
  rw [Int.negOnePow_neg, ← Int.negOnePow_add]
  rfl

/-- At bidegree `(0, 0)`, the filler sign is trivial. -/
theorem fillerSign_zero : fillerSign 0 0 = 1 := rfl

/-- The inverse-rotation counterexample occurs at an odd bidegree sum. -/
theorem fillerSign_zero_one : fillerSign 0 1 = -1 := rfl

/-- Negate the actual period isomorphism; its forward and inverse maps both
change sign. This is the period required after opposite-index duality. -/
def dualPeriod {K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    (period : K ≅ K.bidegreeShift 3 (-3)) : K ≅ K.bidegreeShift 3 (-3) :=
  (-1 : ℤˣ) • period

/-- The unsigned component transport of a signed `(3,-3)` double-complex period. -/
def periodComponent {K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    (period : K ≅ K.bidegreeShift 3 (-3)) (p q p' q' : ℤ)
    (hp : p' = p + 3) (hq : q' = q - 3) : (K.X p).X q ≅ (K.X p').X q' :=
  (p + q).negOnePow •
    ((HomologicalComplex.eval _ _ p ⋙ HomologicalComplex.eval _ _ q).mapIso period ≪≫
    ((HomologicalComplex₂.shiftFunctor₂ AddCommGrpCat (-3)).obj K).shiftFunctor₁XXIso
      p 3 (p + 3) rfl q ≪≫
    K.shiftFunctor₂XXIso (p + 3) q (-3) (q - 3) rfl ≪≫
    eqToIso (congrArg (fun r => (K.X r).X (q - 3)) hp.symm) ≪≫
    eqToIso (congrArg (fun r => (K.X p').X r) hq.symm))

/-- Negating the complex period negates its unsigned component transport. -/
theorem periodComponent_dualPeriod {K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    (period : K ≅ K.bidegreeShift 3 (-3)) (p q p' q' : ℤ)
    (hp : p' = p + 3) (hq : q' = q - 3) :
    (periodComponent (dualPeriod period) p q p' q' hp hq).hom =
      -(periodComponent period p q p' q' hp hq).hom := sorry

/-- The integer identity identifying the first coordinate of the filler term. -/
theorem filler_index₁ (p : ℤ) : p + 1 = (p - 2) + 3 := sorry

/-- The integer identity identifying the second coordinate of the filler term. -/
theorem filler_index₂ (q : ℤ) : q = (q + 3) - 3 := sorry

end Matress

/-- A periodic double complex whose rows and columns are exact and whose
square-filling law uses the parity correction for unsigned shifted maps. -/
def Matress (K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3)) : Prop :=
  (∀ p : ℤ, (K.X p).Acyclic) ∧
    (∀ q : ℤ, (K.flip.X q).Acyclic) ∧
      ∀ (p q : ℤ) (α : (K.X p).X q) (β : (K.X (p - 1)).X (q + 1)),
        (K.X p).d q (q + 1) α = (K.d (p - 1) p).f (q + 1) β →
          ∃ γ : (K.X (p - 2)).X (q + 2),
            (K.d (p - 2) (p - 1)).f (q + 2) γ =
                (K.X (p - 1)).d (q + 1) (q + 2) β ∧
              (Matress.periodComponent period (p - 2) (q + 3) (p + 1) q
                  (Matress.filler_index₁ p) (Matress.filler_index₂ q)).hom
                  ((K.X (p - 2)).d (q + 2) (q + 3) γ) =
                Matress.fillerSign p q • (K.d p (p + 1)).f q α

namespace Matress

/-- Construct a matress from column exactness, row exactness, and its signed filler law. -/
theorem fromProperties (K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3))
    (vertical_exact : ∀ p : ℤ, (K.X p).Acyclic)
    (horizontal_exact : ∀ q : ℤ, (K.flip.X q).Acyclic)
    (filler : ∀ (p q : ℤ) (α : (K.X p).X q) (β : (K.X (p - 1)).X (q + 1)),
      (K.X p).d q (q + 1) α = (K.d (p - 1) p).f (q + 1) β →
        ∃ γ : (K.X (p - 2)).X (q + 2),
          (K.d (p - 2) (p - 1)).f (q + 2) γ = (K.X (p - 1)).d (q + 1) (q + 2) β ∧
            (periodComponent period (p - 2) (q + 3) (p + 1) q
                (filler_index₁ p) (filler_index₂ q)).hom
                ((K.X (p - 2)).d (q + 2) (q + 3) γ) =
                  fillerSign p q • (K.d p (p + 1)).f q α) :
    Matress K period :=
  ⟨vertical_exact, horizontal_exact, filler⟩

/-- Every column and every row of a matress is exact. -/
theorem exact_spec {K : HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ)}
    {period : K ≅ K.bidegreeShift 3 (-3)} (h : Matress K period) :
    (∀ p : ℤ, (K.X p).Acyclic) ∧ (∀ q : ℤ, (K.flip.X q).Acyclic) :=
  ⟨h.1, h.2.1⟩

end Matress

end HomologicalComplex₂

end
