module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic
public import ReasLib.RingTheory.FittingIdeal.BaseChange
public import ReasLib.RingTheory.FittingIdeal.Basic
public import stacks_project.Chap88.Definition_88_8_1_Derived
public import stacks_project.Chap88.Lemma_88_3_3_System
public import stacks_project.Chap88.Lemma_88_4_2_Jacobian

/-!
# Completed Jacobian and Cramer ideals

This leaf owns the completed Jacobian matrix of a kernel family, the Fitting
owners of the Jacobian and Cramer ideals of a finite completed presentation,
and the six named conditions used in the rig-étale TFAE of Lemma 88.8.2.
-/

@[expose] public section

open CategoryTheory
open scoped FittingIdeal

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic
namespace Presentation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {I : Ideal A} {ι : Type u}

/-- The Jacobian matrix in `B` of a family of kernel elements, with rows indexed
by the family and columns indexed by the completed variables. -/
def jacobianMatrix (P : Presentation A B I ι) {κ : Type u} (fs : κ → P.ker) :
    Matrix κ ι B :=
  fun j i ↦ jacobianOnKer P (fs j) i

/-- Entries of the completed Jacobian matrix are the representative Jacobian
values `jacobianOnKer`. -/
theorem jacobianMatrix_apply (P : Presentation A B I ι) {κ : Type u}
    (fs : κ → P.ker) (j : κ) (i : ι) :
    P.jacobianMatrix fs j i = jacobianOnKer P (fs j) i :=
  sorry

/-- The completed Jacobian matrix is the matrix of `jacobianOnKer` values. -/
theorem jacobianMatrix_eq_jacobianOnKer (P : Presentation A B I ι) {κ : Type u}
    (fs : κ → P.ker) :
    P.jacobianMatrix fs = fun j i ↦ jacobianOnKer P (fs j) i :=
  sorry

/-- The Jacobian ideal of a finite completed presentation, as
`Fit_0` of homological degree-zero homology of `naiveCotangent I P`. -/
def jacobianIdeal [Fintype ι] (P : Presentation A B I ι) : Ideal B :=
  fittingIdeal B ((naiveCotangent I P).homology 0 : Type u) 0

/-- The completed Jacobian ideal is `Fit_0` of `H_0(naiveCotangent I P)`. -/
theorem jacobianIdeal_eq [Fintype ι] (P : Presentation A B I ι) :
    P.jacobianIdeal =
      fittingIdeal B ((naiveCotangent I P).homology 0 : Type u) 0 :=
  sorry

/-- For a generating family of `P.ker`, the Jacobian ideal is the ideal of
`Fintype.card ι × Fintype.card ι` minors of the completed Jacobian matrix. -/
theorem jacobianIdeal_eq_minorIdeal [Fintype ι] {κ : Type u}
    (P : Presentation A B I ι) (fs : κ → P.ker)
    (hfs : Ideal.span (Set.range fun j : κ ↦ (fs j : polynomialCompletion A I ι)) =
      P.ker) :
    P.jacobianIdeal = Matrix.minorIdeal (Fintype.card ι) (P.jacobianMatrix fs) :=
  sorry

/-- Containment in the Jacobian ideal is equivalent to containment of every
square minor of a generating family of `P.ker`. -/
theorem jacobianIdeal_le_iff [Fintype ι] {κ : Type u}
    (P : Presentation A B I ι) (fs : κ → P.ker)
    (hfs : Ideal.span (Set.range fun j : κ ↦ (fs j : polynomialCompletion A I ι)) =
      P.ker)
    (J : Ideal B) :
    P.jacobianIdeal ≤ J ↔
      ∀ (rows : Fin (Fintype.card ι) ↪ κ) (cols : Fin (Fintype.card ι) ↪ ι),
        Matrix.det ((P.jacobianMatrix fs).submatrix rows cols) ∈ J :=
  sorry

/-- The Cramer ideal of a finite completed presentation: the image in `B` of
`Fit_r(P.ker)` as a module over `polynomialCompletion A I ι`, where
`r = Fintype.card ι`. -/
def cramerIdeal [Fintype ι] (P : Presentation A B I ι) : Ideal B :=
  Ideal.map P.toAlgHom.toRingHom
    (fittingIdeal (polynomialCompletion A I ι) P.ker (Fintype.card ι))

/-- The Cramer ideal is the extension of `Fit_r(P.ker)` along the presentation. -/
theorem cramerIdeal_eq [Fintype ι] (P : Presentation A B I ι) :
    P.cramerIdeal =
      Ideal.map P.toAlgHom.toRingHom
        (Fit[polynomialCompletion A I ι]_(Fintype.card ι)(P.ker)) :=
  sorry

/-- The Cramer ideal agrees with `Fit_r` of the conormal module `J / J²`. -/
theorem cramerIdeal_eq_fittingCotangent [Fintype ι] (P : Presentation A B I ι) :
    P.cramerIdeal = Fit[B]_(Fintype.card ι)(P.toExtension.Cotangent) :=
  sorry

/-- Containment of the Cramer ideal is equivalent to containment of the image of
`Fit_r(P.ker)`. -/
theorem cramerIdeal_le_iff [Fintype ι] (P : Presentation A B I ι) (J : Ideal B) :
    P.cramerIdeal ≤ J ↔
      Fit[polynomialCompletion A I ι]_(Fintype.card ι)(P.ker) ≤
        J.comap P.toAlgHom.toRingHom :=
  sorry

/-- Multiplication by every element of `I ^ c` is zero on
`naiveCotangentObject I P` in `D(B)`. -/
def powSmulIdEqZero [Fintype ι] (P : Presentation A B I ι) (c : ℕ) : Prop :=
  ∀ a ∈ I ^ c, (algebraMap A B a) • 𝟙 (naiveCotangentObject I P) = 0

/-- Vanishing of `I ^ c` on the derived completed naive cotangent object unpacks
as scalar annihilation of the identity morphism. -/
theorem powSmulIdEqZero_iff [Fintype ι] (P : Presentation A B I ι) (c : ℕ) :
    P.powSmulIdEqZero c ↔
      ∀ a ∈ I ^ c, (algebraMap A B a) • 𝟙 (naiveCotangentObject I P) = 0 :=
  sorry

/-- The extended power `I ^ c` annihilates homology of `naiveCotangent I P` in
homological degrees `1` and `0`. -/
def homologyAnnihilated [Fintype ι] (P : Presentation A B I ι) (c : ℕ) : Prop :=
  (I ^ c).map (algebraMap A B) ≤
      Module.annihilator B ((naiveCotangent I P).homology 1 : Type u) ∧
    (I ^ c).map (algebraMap A B) ≤
      Module.annihilator B ((naiveCotangent I P).homology 0 : Type u)

/-- Annihilation of completed naive cotangent homology unpacks as containment in
both degree `1` and degree `0` annihilators. -/
theorem homologyAnnihilated_iff [Fintype ι] (P : Presentation A B I ι) (c : ℕ) :
    P.homologyAnnihilated c ↔
      (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B ((naiveCotangent I P).homology 1 : Type u) ∧
        (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B ((naiveCotangent I P).homology 0 : Type u) :=
  sorry

/-- Annihilation of chain-complex homology in degrees `1` and `0` is equivalent
to annihilation of derived homology in degrees `-1` and `0`. -/
theorem homologyAnnihilated_iff_derived [Fintype ι] (P : Presentation A B I ι)
    (c : ℕ) :
    P.homologyAnnihilated c ↔
      (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B
            ((DerivedCategory.homologyFunctor (ModuleCat B) (-1)).obj
              (naiveCotangentObject I P)) ∧
        (I ^ c).map (algebraMap A B) ≤
          Module.annihilator B
            ((DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
              (naiveCotangentObject I P)) :=
  sorry

/-- The extended power `I ^ c` annihilates homology of every stage complex
`NL_{B_{n+1}/A_{n+1}}` in homological degrees `1` and `0`. Lean `n : ℕ` is
source index `n ≥ 1`. -/
def stageHomologyAnnihilated [Fintype ι] (P : Presentation A B I ι) (c : ℕ) :
    Prop :=
  ∀ n : ℕ,
    (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
        Module.annihilator (B ⧸ stageIdeal I n)
          ((stageComplex I P n).homology 1 : Type u) ∧
      (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
        Module.annihilator (B ⧸ stageIdeal I n)
          ((stageComplex I P n).homology 0 : Type u)

/-- Stagewise homology annihilation unpacks as containment in both degree `1`
and degree `0` annihilators of every `stageComplex I P n`. -/
theorem stageHomologyAnnihilated_iff [Fintype ι] (P : Presentation A B I ι)
    (c : ℕ) :
    P.stageHomologyAnnihilated c ↔
      ∀ n : ℕ,
        (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
            Module.annihilator (B ⧸ stageIdeal I n)
              ((stageComplex I P n).homology 1 : Type u) ∧
          (I ^ c).map (algebraMap A (B ⧸ stageIdeal I n)) ≤
            Module.annihilator (B ⧸ stageIdeal I n)
              ((stageComplex I P n).homology 0 : Type u) :=
  sorry

/-- For every `a ∈ I`, some power `a ^ c` annihilates
`H_0(naiveCotangent I P)` and `r = Fintype.card ι` kernel elements satisfy the
completed relation condition. -/
def existsRelationGenerators [Fintype ι] (P : Presentation A B I ι) : Prop :=
  ∀ a ∈ I, ∃ c : ℕ,
    algebraMap A B (a ^ c) ∈
        Module.annihilator B ((naiveCotangent I P).homology 0 : Type u) ∧
      ∃ fs : Fin (Fintype.card ι) → P.ker,
        relationCondition P (algebraMap A B (a ^ c)) fs

/-- The Artin pre-pre condition unpacks as annihilation of homological degree
zero together with an `r`-tuple of relations. -/
theorem existsRelationGenerators_iff [Fintype ι] (P : Presentation A B I ι) :
    P.existsRelationGenerators ↔
      ∀ a ∈ I, ∃ c : ℕ,
        algebraMap A B (a ^ c) ∈
            Module.annihilator B ((naiveCotangent I P).homology 0 : Type u) ∧
          ∃ fs : Fin (Fintype.card ι) → P.ker,
            relationCondition P (algebraMap A B (a ^ c)) fs :=
  sorry

/-- For every `a ∈ I`, some power `a ^ c` is elementary for a square completed
Jacobian minor on `r = Fintype.card ι` relations and columns. -/
def existsElementarySquare [Fintype ι] (P : Presentation A B I ι) : Prop :=
  ∀ a ∈ I, ∃ (c : ℕ) (fs : Fin (Fintype.card ι) → P.ker)
      (cols : Fin (Fintype.card ι) ↪ ι),
    IsElementaryFor P (algebraMap A B (a ^ c)) fs cols

/-- The Artin pre condition unpacks as existence of elementary square Jacobian
data for a power of every element of `I`. -/
theorem existsElementarySquare_iff [Fintype ι] (P : Presentation A B I ι) :
    P.existsElementarySquare ↔
      ∀ a ∈ I, ∃ (c : ℕ) (fs : Fin (Fintype.card ι) → P.ker)
          (cols : Fin (Fintype.card ι) ↪ ι),
        IsElementaryFor P (algebraMap A B (a ^ c)) fs cols :=
  sorry

/-- Some extended power `I ^ c` is contained in both the Jacobian ideal and the
Cramer ideal. -/
def fittingContainsPow [Fintype ι] (P : Presentation A B I ι) : Prop :=
  ∃ c : ℕ,
    (I ^ c).map (algebraMap A B) ≤ P.jacobianIdeal ∧
      (I ^ c).map (algebraMap A B) ≤ P.cramerIdeal

/-- Fitting containment unpacks as a single exponent whose extended power lies
in both completed Fitting ideals. -/
theorem fittingContainsPow_iff [Fintype ι] (P : Presentation A B I ι) :
    P.fittingContainsPow ↔
      ∃ c : ℕ,
        (I ^ c).map (algebraMap A B) ≤ P.jacobianIdeal ∧
          (I ^ c).map (algebraMap A B) ≤ P.cramerIdeal :=
  sorry

end Presentation
end Algebra.NaiveCotangent.Adic
