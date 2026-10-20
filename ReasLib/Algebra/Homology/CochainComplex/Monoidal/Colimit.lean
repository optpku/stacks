module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits and tensor products of cochain complexes

When the ambient tensor product preserves colimits in each variable, its coproduct-totalized
tensor product on integer cochain complexes does so as well.  This is the generic cocontinuity
input needed by balanced tensor products of DG bimodule objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w w'

namespace CochainComplex.Monoidal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
variable [MonoidalCategory (CochainComplex C ℤ)]

section Shape

variable {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
variable [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfShape J (tensorRight X)]

/-- Tensoring integer cochain complexes on the left preserves colimits of a fixed shape when
ambient tensoring does. -/
@[stacks 0FPB "left cochain tensor preserves shaped colimits", instance]
theorem tensorLeftPreservesColimitsOfShape (K : CochainComplex C ℤ) :
    PreservesColimitsOfShape J (tensorLeft K) := sorry

/-- Tensoring integer cochain complexes on the right preserves colimits of a fixed shape when
ambient tensoring does. -/
@[stacks 0FPB "right cochain tensor preserves shaped colimits", instance]
theorem tensorRightPreservesColimitsOfShape (K : CochainComplex C ℤ) :
    PreservesColimitsOfShape J (tensorRight K) := sorry

end Shape

section Size

variable [HasColimitsOfSize.{w', w} C]
variable [∀ X : C, PreservesColimitsOfSize.{w', w} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{w', w} (tensorRight X)]

/-- Tensoring integer cochain complexes on the left preserves all colimits in a fixed universe
range when ambient tensoring does. -/
@[stacks 0FPB "left cochain tensor preserves sized colimits", instance]
theorem tensorLeftPreservesColimitsOfSize (K : CochainComplex C ℤ) :
    PreservesColimitsOfSize.{w', w} (tensorLeft K) := sorry

/-- Tensoring integer cochain complexes on the right preserves all colimits in a fixed universe
range when ambient tensoring does. -/
@[stacks 0FPB "right cochain tensor preserves sized colimits", instance]
theorem tensorRightPreservesColimitsOfSize (K : CochainComplex C ℤ) :
    PreservesColimitsOfSize.{w', w} (tensorRight K) := sorry

end Size

section All

variable [HasColimits C]
variable [∀ X : C, PreservesColimits (tensorLeft X)]
variable [∀ X : C, PreservesColimits (tensorRight X)]

/-- Tensoring integer cochain complexes on the left preserves all colimits when ambient
tensoring does. -/
@[stacks 0FPB "left cochain tensor preserves colimits"]
theorem tensorLeftPreservesColimits (K : CochainComplex C ℤ) :
    PreservesColimits (tensorLeft K) := sorry

/-- Tensoring integer cochain complexes on the right preserves all colimits when ambient
tensoring does. -/
@[stacks 0FPB "right cochain tensor preserves colimits"]
theorem tensorRightPreservesColimits (K : CochainComplex C ℤ) :
    PreservesColimits (tensorRight K) := sorry

end All

end CochainComplex.Monoidal

end
