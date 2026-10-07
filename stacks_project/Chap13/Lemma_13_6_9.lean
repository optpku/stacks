module

import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.6.9

The kernel computation for a Verdier quotient, its retract and biproduct
membership views, and its order-theoretic universal property are owned by the
neutral `ObjectProperty.VerdierQuotient` API.
-/

open CategoryTheory

universe v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]

@[stacks 05RK] #check
  (ObjectProperty.VerdierQuotient.kernel_eq_retractClosure P :
    Functor.kernel (ObjectProperty.verdierQuotientFunctor P) = P.retractClosure)

#check
  (ObjectProperty.VerdierQuotient.mem_kernel_iff P :
    ∀ X : D, Functor.kernel (ObjectProperty.verdierQuotientFunctor P) X ↔
      ∃ Y : D, P Y ∧ Nonempty (Retract X Y))

#check
  (ObjectProperty.VerdierQuotient.mem_kernel_iff_biprod P :
    ∀ X : D, Functor.kernel (ObjectProperty.verdierQuotientFunctor P) X ↔
      ∃ (X' Y : D), P Y ∧ Nonempty (X ⊞ X' ≅ Y))

#check
  (ObjectProperty.VerdierQuotient.kernel_le_iff P :
    ∀ (R : ObjectProperty D) [R.IsStableUnderRetracts],
      Functor.kernel (ObjectProperty.verdierQuotientFunctor P) ≤ R ↔ P ≤ R)

end CategoryTheory
