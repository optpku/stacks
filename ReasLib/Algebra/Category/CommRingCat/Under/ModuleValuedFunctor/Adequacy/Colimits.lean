/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Kernel

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor.TensorAdequate

/-- A coproduct of tensor-adequate module-valued functors is tensor adequate. -/
theorem coproduct (A : CommRingCat.{u}) {ι : Type u}
    (F : ι → ModuleValuedFunctor.bundled.{u, u} A) (c : Cofan F)
    (hc : IsColimit c) (hF : ∀ i, ModuleValuedFunctor.TensorAdequate (F i)) :
    ModuleValuedFunctor.TensorAdequate c.pt := sorry

/-- Tensor adequacy is closed under colimits indexed by any small category. -/
theorem closedUnderColimitsOfShape (A : CommRingCat.{u})
    (J : Type u) [SmallCategory J] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (ModuleValuedFunctor.TensorAdequate (A := A)) J := sorry

end ModuleValuedFunctor.TensorAdequate
