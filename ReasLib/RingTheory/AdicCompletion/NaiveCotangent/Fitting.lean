module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Jacobian
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic
public import ReasLib.RingTheory.FittingIdeal.BaseChange
public import ReasLib.RingTheory.FittingIdeal.Basic

/-!
# Completed Jacobian and Cramer ideals

A completed polynomial presentation has a generator-indexed Jacobian matrix,
a Jacobian ideal given by the zeroth Fitting ideal of its degree-zero
cotangent homology, and a Cramer ideal obtained by extending the kernel's
Fitting ideal to the quotient algebra.
-/

open scoped FittingIdeal

@[expose] public section

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

/-- For a finitely generated presentation kernel, the Cramer ideal agrees with
`Fit_r` of the conormal module `J / J²`. -/
theorem cramerIdeal_eq_fittingCotangent [Fintype ι] (P : Presentation A B I ι)
    [Module.Finite (polynomialCompletion A I ι) P.ker] :
    P.cramerIdeal = Fit[B]_(Fintype.card ι)(P.toExtension.Cotangent) :=
  sorry

/-- Containment of the Cramer ideal is equivalent to containment of the image of
`Fit_r(P.ker)`. -/
theorem cramerIdeal_le_iff [Fintype ι] (P : Presentation A B I ι) (J : Ideal B) :
    P.cramerIdeal ≤ J ↔
      Fit[polynomialCompletion A I ι]_(Fintype.card ι)(P.ker) ≤
        J.comap P.toAlgHom.toRingHom :=
  sorry

end Presentation
end Algebra.NaiveCotangent.Adic
