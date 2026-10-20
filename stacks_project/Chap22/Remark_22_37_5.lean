/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Endomorphism
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uA uC vC uD vD

section Compact

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]
variable (e : C ≌ D) (X : C)
variable [e.functor.Additive]

/- Remark 22.37.5 (1): an additive equivalence preserves compact objects. Applied to the
regular object `A`, this says that `N = F(A)` is compact. -/
@[stacks 09S9] #check e.isCompactObject_obj X

end Compact

section Generator

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable (e : C ≌ D)
variable [e.functor.PreservesZeroMorphisms] [e.inverse.PreservesZeroMorphisms]
variable [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
variable (X : C)

/- Remark 22.37.5 (2): a shift-compatible equivalence preserves weak generators. Applied to
the regular object `A`, this says that `N = F(A)` generates the target derived category. -/
@[stacks 09S9] #check e.isWeakGenerator_obj X

end Generator

section SelfExt

variable {R : Type uR} [CommRing R]
variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]
variable [Linear R C] [Linear R D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable (e : C ≌ D)
variable [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
variable (X : C) (Y : D) (h : e.functor.obj X ≅ Y) (k : ℤ)

/- Remark 22.37.5 (3): an additive `R`-linear shift-compatible equivalence identifies every shifted
self-Hom module of `A` with that of `N = F(A)`. -/
@[stacks 09S9] #check
  (e.selfShiftLinearEquiv h k :
    (X ⟶ X⟦k⟧) ≃ₗ[R] (Y ⟶ Y⟦k⟧))

end SelfExt

section Bimodule

variable {R : Type uR} [CommRing R]
variable (A B : CochainDGAlgebra.{uR, uA} R)
variable (N : DifferentialGradedModule B)

/- Remark 22.37.5 (4): the extra structure needed on a differential graded right `B`-module
is a compatible left differential graded `A`-action, canonically modeled by
`DifferentialGradedBimodule.LeftAction A N`. -/
@[stacks 09S9] #check DifferentialGradedBimodule.LeftAction A N

#check
  (DifferentialGradedBimodule.LeftAction.equivEndomorphismDGAHom A N :
    DifferentialGradedBimodule.LeftAction A N ≃
      CochainDGAlgebra.Hom A N.endomorphismDGA)

end Bimodule
