module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor.Isomorphism
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed

/-! # Derived pullback and internal Hom -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.DerivedCategory CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The canonical pullback/internal-Hom map is the transpose of pulled-back evaluation,
using the structure-ring derived tensor and explicit ambient tensor models. -/
def pullbackComparison (g' : X' ⟶ X)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M K : ModuleDerived X) :
    (LeftDerived.Homotopy.functor (Modules.pullback g')).obj ((H_X.ihomOf M).obj K) ⟶
      (H_X'.ihomOf ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).obj
        ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj K) :=
  (DerivedTensor.Right.Closed.adjunctionOf H_X' T_X'
    ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).homEquiv _ _
    ((DerivedQCoh.rightTensorComparisonIso g' ((H_X.ihomOf M).obj K) M).inv ≫
      (LeftDerived.Homotopy.functor (Modules.pullback g')).map
        ((DerivedTensor.Right.Closed.adjunctionOf H_X T_X M).counit.app K))

/-- Transposing the pullback/internal-Hom comparison recovers the inverse tensor comparison
followed by pullback of evaluation. -/
theorem pullbackComparison_spec (g' : X' ⟶ X)
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (T_X : DerivedTensor.Right.Monoidal.Model (C := X.Modules))
    (T_X' : DerivedTensor.Right.Monoidal.Model (C := X'.Modules))
    (M K : ModuleDerived X) :
    ((DerivedTensor.Right.Closed.adjunctionOf H_X' T_X'
      ((LeftDerived.Homotopy.functor (Modules.pullback g')).obj M)).homEquiv _ _).symm
        (pullbackComparison g' H_X H_X' T_X T_X' M K) =
      (DerivedQCoh.rightTensorComparisonIso g' ((H_X.ihomOf M).obj K) M).inv ≫
        (LeftDerived.Homotopy.functor (Modules.pullback g')).map
          ((DerivedTensor.Right.Closed.adjunctionOf H_X T_X M).counit.app K) :=
  Equiv.symm_apply_apply _ _

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
