/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
variable (M' : DifferentialGradedModule A)
variable (M : LeftDifferentialGradedModule A)
variable (N : CochainComplex (ModuleCat.{v} R) ℤ)

/- Lemma 22.13.2 (0FQ4): morphisms from a right DG module into the internal Hom from a
left DG module are canonically equivalent to morphisms out of their relative tensor complex. -/
@[stacks 0FQ4] #check
  (OfLeft.homEquiv M' M N :
    (M' ⟶ OfLeft.obj M N) ≃ (TensorProduct.complex M' M ⟶ N))

/- The equivalence is functorial in both variables through the concrete tensor--Hom
adjunction. -/
#check @OfLeft.adjunction

end DifferentialGradedModule.InternalHom
