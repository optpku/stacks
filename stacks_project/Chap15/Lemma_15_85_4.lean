/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.MorphismRepresentative
import StacksCheckRecall

/-!
# Lemma 15.85.4

The four source clauses are owned by
`CategoryTheory.DerivedCategory.TwoTermMorphism`: localization is fully faithful on the indicated
bounded complexes, the two-term `Ext¹` vanishing criterion is a degree-zero homotopy condition,
and derived morphisms admit representatives with a prescribed degree-`-2` component, unique up
to the displayed two-step homotopy.

@stack 0ALN
-/

@[expose] public section

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle

universe u

@[stacks 0ALN "Lemma 15.85.4 (1)"]
#check fun {R : Type u} [Ring R]
    {M K : CochainComplex (ModuleCat R) ℤ}
    (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-1)) =>
  (CategoryTheory.DerivedCategory.TwoTermMorphism.comparison_bijective hM hM0 hK :
    Function.Bijective
      (_root_.DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj M ⟶
          (HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj K) →
            (_root_.DerivedCategory.Q.obj M ⟶ _root_.DerivedCategory.Q.obj K)))

@[stacks 0ALN "Lemma 15.85.4 (2)"]
#check fun {R : Type u} [Ring R]
    {M K : CochainComplex (ModuleCat R) ℤ}
    (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hKge : K.IsStrictlyGE (-1)) (hKle : K.IsStrictlyLE 0)
    (hK0 : Projective (K.X 0)) (a : M ⟶ K) =>
  (CategoryTheory.DerivedCategory.TwoTermMorphism.extOne_precomposition_eq_zero_iff
      hM hM0 hKge hKle hK0 a :
    (∀ (N : ModuleCat R)
      (e : ShiftedHom (_root_.DerivedCategory.Q.obj K)
        ((_root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) (1 : ℤ)),
      _root_.DerivedCategory.Q.map a ≫ e = 0) ↔
        ∃ h0 : M.X 0 ⟶ K.X (-1), a.f (-1) + M.d (-1) 0 ≫ h0 = 0)

@[stacks 0ALN "Lemma 15.85.4 (3)"]
#check fun {R : Type u} [Ring R]
    {M K : CochainComplex (ModuleCat R) ℤ}
    (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    (α : _root_.DerivedCategory.Q.obj M ⟶ _root_.DerivedCategory.Q.obj K)
    (a : M.X (-2) ⟶ K.X (-2)) (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ CategoryTheory.DerivedCategory.TwoTermMorphism.negTwoProjection K hK =
      CategoryTheory.DerivedCategory.TwoTermMorphism.negTwoCocycleToShift a ha) =>
  (CategoryTheory.DerivedCategory.TwoTermMorphism.exists_representative_with_negTwo
      hM hM0 hK α a ha hα :
    ∃ aMap : M ⟶ K, _root_.DerivedCategory.Q.map aMap = α ∧ aMap.f (-2) = a)

@[stacks 0ALN "Lemma 15.85.4 (4)"]
#check fun {R : Type u} [Ring R]
    {M K : CochainComplex (ModuleCat R) ℤ}
    (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2)) {aMap aMap' : M ⟶ K}
    (hQ : _root_.DerivedCategory.Q.map aMap = _root_.DerivedCategory.Q.map aMap')
    (hnegTwo : aMap.f (-2) = aMap'.f (-2)) =>
  (CategoryTheory.DerivedCategory.TwoTermMorphism.representatives_homotopic
      hM hM0 hK hQ hnegTwo :
    ∃ h : Homotopy aMap' aMap,
      M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 ∧
        aMap'.f (-1) = aMap.f (-1) + h.hom (-1) (-2) ≫ K.d (-2) (-1) +
          M.d (-1) 0 ≫ h.hom 0 (-1) ∧
        aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0)

#check @CategoryTheory.DerivedCategory.TwoTermMorphism.negTwoCocycleToShift
#check @CategoryTheory.DerivedCategory.TwoTermMorphism.negTwoProjection
