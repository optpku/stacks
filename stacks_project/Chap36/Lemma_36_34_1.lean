/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Algebra.Algebra.Opposite
import Mathlib.LinearAlgebra.Basis.MulOpposite
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Restriction.FiniteFree
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

variable {A R : Type u} [CommRing A] [Ring R] [Algebra A R]
variable [Module.Free A R] [Module.Finite A R]

/- Lemma 36.34.1: if `R` is an `A`-algebra which is finite free as an `A`-module,
then a derived right `R`-module which is pseudo-coherent after restriction to `A`
has a bounded-above representative by finite free right `R`-modules. -/
@[stacks 0CSF] #check
  (CategoryTheory.DerivedCategory.IsPseudoCoherent.exists_finiteFree_model_of_restrictScalars_of_finiteFree
    (A := A) (B := Rᵐᵒᵖ) :
    (M : DerivedCategory (ModuleCat Rᵐᵒᵖ)) →
      ((ModuleCat.restrictScalars
        (algebraMap A Rᵐᵒᵖ)).mapDerivedCategory.obj M).IsPseudoCoherent →
      ∃ (P : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ) (_ : DerivedCategory.Q.obj P ≅ M),
        CochainComplex.minus (ModuleCat Rᵐᵒᵖ) P ∧ P.IsTermwiseFiniteFree)
