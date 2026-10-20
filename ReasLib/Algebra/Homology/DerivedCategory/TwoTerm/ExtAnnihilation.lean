module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.Representative
public import ReasLib.CategoryTheory.DerivedCategory.Ext.Single
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext annihilation for two-term complexes

This file owns the equivalent Ext-annihilation and differential-factorization conditions for a
derived module concentrated in degrees `-1` and `0`.

@stack 0G9F
@stack 0G9J
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.Ext
open scoped DerivedExt

noncomputable section

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

/-- Scalar multiplication by `a` on degree `-1` factors through the differential
`P⁻¹ ⟶ P⁰`. -/
@[stacks 0G9F "scalar factorization through a two-term differential"]
def smulFactorsThroughDifferentialAtNegOne
    (P : CochainComplex (ModuleCat R) ℤ) (a : R) : Prop :=
  ∃ h : P.X 0 ⟶ P.X (-1),
    P.d (-1) 0 ≫ h = ModuleCat.ofHom (LinearMap.lsmul R (P.X (-1)) a)

/-- The ideal `I` annihilates `Ext¹_R(K, N)` for every `R`-module `N`. -/
@[stacks 0G9F "Ext-one annihilation"]
def twoTermExtOneAnnihilatedByIdeal
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) : Prop :=
  ∀ N : ModuleCat R, I ≤ Module.annihilator R ((moduleFunctor K (1 : ℤ)).obj N)

/-- Ext-one annihilation is equivalent to vanishing of postcomposition by every scalar in the
ideal. -/
@[stacks 0G9F "Ext-one annihilation formula"]
theorem twoTermExtOneAnnihilatedByIdeal_iff
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) :
    twoTermExtOneAnnihilatedByIdeal K I ↔
      ∀ (N : ModuleCat R) (a : I)
        (e : Ext⁽(1 : ℤ)⁾(K,
          (_root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)),
        e.comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((_root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).map
              (ModuleCat.ofHom (LinearMap.lsmul R N (a : R)))))
          (zero_add (1 : ℤ)) = 0 := sorry
/- Proof strategy: unfold the annihilator condition and the module structure on
`moduleFunctor K 1`.  Identify scalar multiplication on an Ext class with composition by the
shifted single-complex morphism induced by `LinearMap.lsmul`, then simplify the degree shift. -/

/-- There is a free two-term representative on which every scalar in `I` factors through the
differential. -/
@[stacks 0G9F "free representative factorization condition"]
def admits_two_term_free_representative_with_ideal_factorization
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) : Prop :=
  ∃ P : CochainComplex (ModuleCat R) ℤ,
    IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0) ∧
      ∀ a : I, smulFactorsThroughDifferentialAtNegOne P (a : R)

/-- Every projective two-term representative has the scalar-factorization property for `I`. -/
@[stacks 0G9F "projective representative factorization condition"]
def all_two_term_projective_representatives_have_ideal_factorization
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) : Prop :=
  ∀ (P : CochainComplex (ModuleCat R) ℤ)
    (_ : IsTwoTermRepresentative K P) (_ : Projective (P.X 0)) (a : I),
    smulFactorsThroughDifferentialAtNegOne P (a : R)

/-- The ideal `I` annihilates `Ext¹_R(K, N)` for every finite `R`-module `N`. -/
@[stacks 0G9F "Ext-one annihilation on finite modules"]
def twoTermExtOneAnnihilatedByIdealOnFiniteModules
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) : Prop :=
  ∀ (N : ModuleCat R) (_ : Module.Finite R N),
    I ≤ Module.annihilator R ((moduleFunctor K (1 : ℤ)).obj N)

/-- Ext-one annihilation on finite modules is equivalent to the corresponding composition
formula on finite test modules. -/
@[stacks 0G9F "finite-module Ext-one annihilation formula"]
theorem twoTermExtOneAnnihilatedByIdealOnFiniteModules_iff
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) :
    twoTermExtOneAnnihilatedByIdealOnFiniteModules K I ↔
      ∀ (N : ModuleCat R) (_ : Module.Finite R N)
        (a : I) (e : Ext⁽(1 : ℤ)⁾(K,
          (_root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)),
        e.comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((_root_.DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).map
              (ModuleCat.ofHom (LinearMap.lsmul R N (a : R)))))
          (zero_add (1 : ℤ)) = 0 := sorry
/- Proof strategy: repeat `twoTermExtOneAnnihilatedByIdeal_iff` with the finite-module binder;
unfold the restricted predicate and use the same scalar-action/composition formula pointwise. -/

/-- There is a finite free two-term representative, finite also in degree `-1`, on which every
scalar in `I` factors through the differential. -/
@[stacks 0G9F "finite free representative factorization condition"]
def admits_two_term_finite_free_representative_with_ideal_factorization
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R) : Prop :=
  ∃ P : CochainComplex (ModuleCat R) ℤ,
    IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0) ∧ Module.Finite R (P.X 0) ∧
      Module.Finite R (P.X (-1)) ∧
        ∀ a : I, smulFactorsThroughDifferentialAtNegOne P (a : R)

/-- Ext-one annihilation, existence of a free representative
with scalar factorization, and scalar factorization for every projective representative are
equivalent. -/
@[stacks 0G9F "Lemma 15.85.5, equivalence (1)-(3)"]
theorem two_term_ext1_annihilated_tfae
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) :
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K I,
      admits_two_term_free_representative_with_ideal_factorization K I,
      all_two_term_projective_representatives_have_ideal_factorization K I
    ] := sorry
/- Proof strategy: choose a free two-term representative with `IsTwoTermRepresentative.exists_free`.
Use `TwoTermMorphism.extOne_precomposition_eq_zero_iff` to translate scalar annihilation into
factorization through its differential; transport the factorization between projective
representatives via the homotopy comparison, then close the three implications with
`List.tfae_finish`. -/

/-- Over a Noetherian ring, the three basic conditions are also equivalent
to finite-test-module annihilation and to a finite two-term representative with scalar
factorization. -/
@[stacks 0G9F "Lemma 15.85.5, Noetherian equivalence (1)-(5)"]
theorem two_term_ext1_annihilated_tfae_of_isNoetherianRing
    [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K))
    (hH0 : Module.Finite R
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) :
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K I,
      admits_two_term_free_representative_with_ideal_factorization K I,
      all_two_term_projective_representatives_have_ideal_factorization K I,
      twoTermExtOneAnnihilatedByIdealOnFiniteModules K I,
      admits_two_term_finite_free_representative_with_ideal_factorization K I
    ] := sorry
/- Proof strategy: start from `two_term_ext1_annihilated_tfae`; use
`IsTwoTermRepresentative.exists_finiteFree` to obtain the finite representative and the
Noetherian finite-test theorem for the coherent Ext-one functor to pass between all modules and
finite modules.  Assemble all five implications with `List.tfae_finish`. -/

/-- An isomorphism on `H⁰` and an epimorphism on `H⁻¹` transfer the
Ext-one annihilation condition between two derived modules supported in degrees `-1` and `0`. -/
@[stacks 0G9J "Lemma 15.85.9"]
theorem twoTermExtOneAnnihilatedByIdeal_of_h0_iso_of_hneg1_epi
    (I : Ideal R) {K K' : DerivedCategory (ModuleCat R)} (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) 0).map α))
    (hαneg1 : Epi ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) (-1)).map α))
    (hI : twoTermExtOneAnnihilatedByIdeal K I) :
    twoTermExtOneAnnihilatedByIdeal K' I := sorry
/- Proof strategy: use naturality of the degree-one Ext functor to compare scalar actions after
precomposition with `α`.  The two-term endomorphism cancellation theorem makes this
precomposition faithful under the `H⁰`-isomorphism and `H⁻¹`-epimorphism hypotheses, so the
annihilation formula for `K` transfers to `K'`. -/

end

end CategoryTheory
