/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InternalHom.Adjunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace DifferentialGradedModule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (M : DifferentialGradedModule A)
variable (M' : LeftDifferentialGradedModule A)
variable (N : CochainComplex (ModuleCat.{v} R) ℤ)

/- Lemma 22.13.4 (0FQ6): morphisms from a left DG module into the internal Hom from a
right DG module are canonically equivalent to morphisms out of their relative tensor complex;
the Koszul tensor-order convention is built into the concrete owner. -/
@[stacks 0FQ6] #check
  (OfRight.homEquiv M M' N :
    (M' ⟶ OfRight.obj M N) ≃ (TensorProduct.complex M M' ⟶ N))

/- The equivalence is functorial in both variables through the concrete tensor--Hom
adjunction. -/
#check @OfRight.adjunction

end DifferentialGradedModule.InternalHom
