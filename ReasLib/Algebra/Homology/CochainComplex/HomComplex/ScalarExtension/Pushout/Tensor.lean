/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.ScalarExtension.Pushout
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom complexes after tensor-product base change

This leaf specializes the support and relative-flatness API to
`A' = A ⊗[R] R'`.  It uses the shared scoped right tensor-algebra owner, so downstream users do not
need to install an ambient global instance merely to state the canonical base-change conclusions.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open scoped TensorProduct Algebra.TensorProduct.Right

namespace CochainComplex.HomComplex.Pushout.Tensor

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- Scalar extension to the tensor-product pushout preserves the lower support bound of the Hom
complex.  This specialization uses the shared `Algebra.TensorProduct.Right` scope. -/
@[stacks 0E1U "bounded-below Hom model after tensor-product base change"]
theorem plus
    {P F : CochainComplex (ModuleCat A) ℤ}
    (hE : CochainComplex.plus (ModuleCat A)
      (CochainComplex.HomComplex.moduleComplex A P F)) :
    CochainComplex.plus (ModuleCat (A ⊗[R] R'))
      ((CochainComplex.HomComplex.ScalarExtension.functor
        (algebraMap A (A ⊗[R] R'))).obj
          (CochainComplex.HomComplex.moduleComplex A P F)) := sorry
/- Proof strategy: specialize `CochainComplex.HomComplex.ScalarExtension.plus` to
`algebraMap A (A ⊗[R] R')`. -/

/-- After tensor-product base change, a bounded Hom model built from a relatively flat target is
termwise flat over the new base ring.  Flatness of `A` over `R` is not required for this termwise
conclusion. -/
@[stacks 0E1U "relative flatness of a Hom model after tensor-product base change"]
theorem isTermwiseFlatOver
    (P F : CochainComplex (ModuleCat A) ℤ)
    (hP : CochainComplex.minus (ModuleCat A) P)
    (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.plus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    ((CochainComplex.HomComplex.ScalarExtension.functor
      (algebraMap A (A ⊗[R] R'))).obj
        (CochainComplex.HomComplex.moduleComplex A P F)).IsTermwiseFlatOver R' := sorry
/- Proof strategy: specialize the generic pushout flatness theorem and discharge the canonical
pushout instance with `Algebra.TensorProduct.Right`. -/

end CochainComplex.HomComplex.Pushout.Tensor
