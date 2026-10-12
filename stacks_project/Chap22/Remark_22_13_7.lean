/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InternalHom.Shift
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CochainComplex.HomComplex

variable {R : Type u} [CommRing R]

section Complex

variable (M N : CochainComplex (ModuleCat.{v} R) ℤ) (k : ℤ)

/- Remark 22.13.7 (0FQ9) (1): the canonical first-variable shift map is an isomorphism
`Hom^•(M, N)[-k] ≅ Hom^•(M⟦k⟧, N)` of cochain complexes of `R`-modules. -/
@[stacks 0FQ9 "underlying Hom-complex isomorphism"] #check
  (CochainComplex.HomComplex.leftShiftIso R M N k :
    (CochainComplex.HomComplex.moduleComplex R M N)⟦-k⟧ ≅
      CochainComplex.HomComplex.moduleComplex R (M⟦k⟧) N)

end Complex

section OfLeft

variable {A : CochainDGAlgebra.{u, v} R}
  {M N : CochainComplex (ModuleCat.{v} R) ℤ}
variable (rho : LeftDifferentialGradedModule.ActionOn A M) (k : ℤ)

/- Remark 22.13.7 (0FQ9) (2): the canonical first-variable shift isomorphism
`Hom^•(M, N)[-k] ≅ Hom^•(M⟦k⟧, N)` respects the induced right differential graded
`A`-module structures when `M` is a left DG module. -/
@[stacks 0FQ9 "lift from a left action"] #check
  (DifferentialGradedModule.InternalHom.OfLeft.Action.shiftIso N rho k :
    DifferentialGradedModule.InternalHom.OfLeft.Action.shiftedRight N rho k ≅
      DifferentialGradedModule.InternalHom.OfLeft.Action.shiftedSourceRight N rho k)

end OfLeft

section OfRight

variable {A : CochainDGAlgebra.{u, v} R}
  {M N : CochainComplex (ModuleCat.{v} R) ℤ}
variable (rho : DifferentialGradedModule.ActionOn A M) (k : ℤ)

/- Remark 22.13.7 (0FQ9) (3): the canonical first-variable shift isomorphism
`Hom^•(M, N)[-k] ≅ Hom^•(M⟦k⟧, N)` respects the induced left differential graded
`A`-module structures when `M` is a right DG module. -/
@[stacks 0FQ9 "lift from a right action"] #check
  (DifferentialGradedModule.InternalHom.OfRight.Action.shiftIso N rho k :
    DifferentialGradedModule.InternalHom.OfRight.Action.shiftedLeft N rho k ≅
      DifferentialGradedModule.InternalHom.OfRight.Action.shiftedSourceLeft N rho k)

/- The source of the right-action comparison uses the global signed shift of left DG modules. -/
#check @LeftDifferentialGradedModule.shift_smul_apply
#check
  (CategoryTheory.shiftEquiv (LeftDifferentialGradedModule A) k :
    LeftDifferentialGradedModule A ≌ LeftDifferentialGradedModule A)

end OfRight
