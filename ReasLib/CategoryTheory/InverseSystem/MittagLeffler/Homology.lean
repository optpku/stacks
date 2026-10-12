/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Limits

/-!
# Homology of limits of Mittag-Leffler complexes

This leaf exposes the degree-uniform comparison between homology of a sequential limit and the
limit of homology.  The comparison morphism is mathlib's canonical `limit.post` map.
@stack 0918
-/

@[expose] public section

open CategoryTheory.Limits ComplexShape

noncomputable section

universe v

namespace CategoryTheory.SequentialInverseSystem

namespace LimitHomology

/-- The Milnor short exact row for homology of a sequential inverse limit, under the three
vanishing hypotheses in the degree window `n - 2`, `n - 1`, and `H (n - 1)`.  The comparison map is
the canonical `limit.post`; the left term is the neutral canonical Milnor cokernel owner. -/
theorem shortExact_of_r1Vanishing
    (A : SequentialInverseSystem (CochainComplex AddCommGrpCat.{v} ℤ)) (n : ℤ)
    (hprev₂ : IsZero
      (Milnor.ProductCone.canonicalR1
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 2))))
    (hprev₁ : IsZero
      (Milnor.ProductCone.canonicalR1
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1))))
    (hHprev : IsZero
      (Milnor.ProductCone.canonicalR1
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) (n - 1)))) :
    ∃ (ι :
        Milnor.ProductCone.canonicalR1
          (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) (n - 1)) ⟶
          (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) n).obj (limit A))
      (hι :
        ι ≫ limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) n) = 0),
      (ShortComplex.mk ι (limit.post A
        (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) n)) hι).ShortExact := sorry

/-- Lemma 15.87.3 (0918), in degree-uniform form: under the three `R¹ lim` vanishing
hypotheses, homology commutes with the sequential inverse limit in degree `n`. -/
@[stacks 0918]
theorem isIso_of_r1Vanishing
    (A : SequentialInverseSystem (CochainComplex AddCommGrpCat.{v} ℤ)) (n : ℤ)
    (hprev₂ : IsZero
      (Milnor.ProductCone.canonicalR1
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 2))))
    (hprev₁ : IsZero
      (Milnor.ProductCone.canonicalR1
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1))))
    (hHprev : IsZero
      (Milnor.ProductCone.canonicalR1
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) (n - 1)))) :
    IsIso (limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) n)) := sorry

/-- The preceding comparison isomorphism follows from the corresponding three Mittag--Leffler
conditions via the neutral canonical Milnor cokernel owner. -/
theorem isIso_of_mittagLeffler
    (A : SequentialInverseSystem (CochainComplex AddCommGrpCat.{v} ℤ)) (n : ℤ)
    (hprev₂ : SequentialInverseSystem.IsMittagLeffler
      (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 2)))
    (hprev₁ : SequentialInverseSystem.IsMittagLeffler
      (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)))
    (hHprev : SequentialInverseSystem.IsMittagLeffler
      (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) (n - 1))) :
    IsIso (limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) n)) := sorry

/-- Homology in degree `n` commutes with a sequential inverse limit of cochain complexes of
abelian groups when the two preceding degree towers are Mittag-Leffler and the preceding
homology tower is essentially constant. -/
@[stacks 070E]
theorem isIso
    (A : SequentialInverseSystem (CochainComplex AddCommGrpCat.{v} ℤ)) (n : ℤ)
    (hprev₂ : SequentialInverseSystem.IsMittagLeffler
      (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 2)))
    (hprev₁ : SequentialInverseSystem.IsMittagLeffler
      (A ⋙ HomologicalComplex.eval AddCommGrpCat (up ℤ) (n - 1)))
    (hHprev : IsCofiltered.IsEssentiallyConstant
      (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) (n - 1))) :
    IsIso (limit.post A (HomologicalComplex.homologyFunctor AddCommGrpCat (up ℤ) n)) := sorry

end LimitHomology

end CategoryTheory.SequentialInverseSystem
