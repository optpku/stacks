/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.Representative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms from bounded-above complexes to two-term targets

This file owns the comparison between homotopy-category and derived-category morphisms used to
describe maps out of a complex whose degree-zero term is projective.  It also records the
degree-`-2` cocycle and projection maps used to prescribe a representative component.

@stack 0ALN
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle

universe u

namespace CategoryTheory.DerivedCategory.TwoTermMorphism

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)
local notation "single₀" => _root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The degree identity placing a degree-`-2` component in a degree-two cocycle. -/
@[stacks 0ALN "degree-minus-two cocycle identity"]
theorem negTwo_add_two_eq_zero : (-2 : ℤ) + 2 = 0 := sorry
/- Proof strategy: normalize the integer expression with the canonical additive arithmetic
simplifier. -/

/-- The predecessor identity used by the degree-`-2` cocycle constructor. -/
@[stacks 0ALN "degree-minus-three predecessor identity"]
theorem negThree_add_one_eq_negTwo : (-3 : ℤ) + 1 = -2 := sorry
/- Proof strategy: normalize the integer expression with the canonical additive arithmetic
simplifier. -/

/-- The derived morphism to `K⁻²[2]` determined by a degree-`-2` cocycle `a`. -/
@[stacks 0ALN "degree-minus-two cocycle morphism"]
abbrev negTwoCocycleToShift {M K : Cpx}
    (a : M.X (-2) ⟶ K.X (-2)) (ha : M.d (-3) (-2) ≫ a = 0) :=
  _root_.DerivedCategory.Q.map
    (equivHomShift.symm
      (toSingleMk a negTwo_add_two_eq_zero (-3) negThree_add_one_eq_negTwo ha)) ≫
    ((_root_.DerivedCategory.Q.commShiftIso (2 : ℤ)).app
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom ≫
    (((_root_.DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

/-- The identity of `K⁻²` is a cocycle when `K` vanishes below degree `-2`. -/
@[stacks 0ALN "degree-minus-two projection cocycle"]
theorem negTwoProjection_cocycle (K : Cpx) (hK : K.IsStrictlyGE (-2)) :
    K.d (-3) (-2) ≫ 𝟙 (K.X (-2)) = 0 := sorry
/- Proof strategy: strict support below degree `-2` makes `K.X (-3)` a zero object; rewrite the
differential through that zero object and simplify composition with the identity. -/

/-- The canonical derived projection from `K` to `K⁻²[2]` for a complex supported in
degrees `≥ -2`. -/
@[stacks 0ALN "degree-minus-two projection"]
abbrev negTwoProjection (K : Cpx) (hK : K.IsStrictlyGE (-2)) :=
  _root_.DerivedCategory.Q.map
    (equivHomShift.symm
      (toSingleMk (𝟙 (K.X (-2))) negTwo_add_two_eq_zero (-3)
        negThree_add_one_eq_negTwo (negTwoProjection_cocycle K hK))) ≫
    ((_root_.DerivedCategory.Q.commShiftIso (2 : ℤ)).app
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj (K.X (-2)))).hom ≫
    (((_root_.DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (K.X (-2))).symm.hom⟦(2 : ℤ)⟧')

/-- Lemma 15.85.4 (1): if `M` is supported in degrees `≤ 0` with projective degree-zero
term and `K` is supported in degrees `≥ -1`, localization induces a bijection from homotopy
classes of maps `M ⟶ K` to derived morphisms. -/
@[stacks 0ALN "Lemma 15.85.4 (1)"]
theorem comparison_bijective
    {M K : Cpx} (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-1)) :
    Function.Bijective
      (_root_.DerivedCategory.Qh.map : ((KQ).obj M ⟶ (KQ).obj K) → _) := sorry
/- Proof strategy: apply the localization comparison theorem for a bounded-above source whose
degree-zero term is projective.  Use the strict support hypotheses to reduce the lifting and
homotopy obstructions to degree zero, where projectivity of `M.X 0` supplies the lift. -/

/-- Lemma 15.85.4 (2): for a two-term target with projective degree-zero term, vanishing of
precomposition on every `Ext¹` group is equivalent to a degree-zero homotopy correction. -/
@[stacks 0ALN "Lemma 15.85.4 (2)"]
theorem extOne_precomposition_eq_zero_iff
    {M K : Cpx} (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hKge : K.IsStrictlyGE (-1)) (hKle : K.IsStrictlyLE 0)
    (hK0 : Projective (K.X 0)) (a : M ⟶ K) :
    (∀ (N : ModuleCat R)
      (e : ShiftedHom (_root_.DerivedCategory.Q.obj K) ((single₀).obj N) (1 : ℤ)),
      _root_.DerivedCategory.Q.map a ≫ e = 0) ↔
      ∃ h0 : M.X 0 ⟶ K.X (-1), a.f (-1) + M.d (-1) 0 ≫ h0 = 0 := sorry
/- Proof strategy: represent every degree-one Ext class by a map to a shifted degree-zero single
complex.  Use `comparison_bijective` to work in the homotopy category; the vanishing of all
precomposites is exactly the existence of the displayed degree-zero homotopy correction, with
projectivity of `M.X 0` and `K.X 0` resolving the endpoint lifts. -/

/-- Lemma 15.85.4 (3): a derived morphism whose projection to `K⁻²[2]` is represented by
a prescribed cocycle has a cochain representative with that degree-`-2` component. -/
@[stacks 0ALN "Lemma 15.85.4 (3)"]
theorem exists_representative_with_negTwo
    {M K : Cpx} (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2))
    (α : _root_.DerivedCategory.Q.obj M ⟶ _root_.DerivedCategory.Q.obj K)
    (a : M.X (-2) ⟶ K.X (-2)) (ha : M.d (-3) (-2) ≫ a = 0)
    (hα : α ≫ negTwoProjection K hK = negTwoCocycleToShift a ha) :
    ∃ aMap : M ⟶ K,
      _root_.DerivedCategory.Q.map aMap = α ∧ aMap.f (-2) = a := sorry
/- Proof strategy: choose a cochain representative of `α` via the localization comparison after
replacing the target below degree `-1`; the equality with `negTwoCocycleToShift` says that the
difference of its degree-`-2` component and `a` is null-homotopic.  Correct the representative by
that homotopy without changing its derived image. -/

/-- Lemma 15.85.4 (4): two representatives of the same derived morphism with equal
degree-`-2` components differ by a homotopy whose only relevant components satisfy the displayed
degree-`-2`, degree-`-1`, and degree-zero formulas. -/
@[stacks 0ALN "Lemma 15.85.4 (4)"]
theorem representatives_homotopic
    {M K : Cpx} (hM : M.IsStrictlyLE 0) (hM0 : Projective (M.X 0))
    (hK : K.IsStrictlyGE (-2)) {aMap aMap' : M ⟶ K}
    (hQ : _root_.DerivedCategory.Q.map aMap = _root_.DerivedCategory.Q.map aMap')
    (hnegTwo : aMap.f (-2) = aMap'.f (-2)) :
    ∃ h : Homotopy aMap' aMap,
      M.d (-2) (-1) ≫ h.hom (-1) (-2) = 0 ∧
        aMap'.f (-1) =
          aMap.f (-1) + h.hom (-1) (-2) ≫ K.d (-2) (-1) +
            M.d (-1) 0 ≫ h.hom 0 (-1) ∧
        aMap'.f 0 = aMap.f 0 + h.hom 0 (-1) ≫ K.d (-1) 0 := sorry
/- Proof strategy: use injectivity in `comparison_bijective` to obtain a homotopy between the two
cochain maps.  Modify the degree-`-2` homotopy component using `hnegTwo`, then expand the homotopy
equations in degrees `-2`, `-1`, and `0`; strict support removes every other component. -/

end

end CategoryTheory.DerivedCategory.TwoTermMorphism
