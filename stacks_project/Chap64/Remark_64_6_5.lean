/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.InjectiveHomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived
namespace Bounded

variable {A : Type uA}
  [Category.{vA} A] [Abelian A]
variable {B : Type uB}
  [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] [EnoughInjectives A] [Limits.PreservesFiniteLimits F]
  (K : CochainComplex.Plus A) [∀ n : ℤ, Injective (K.obj.X n)] (i : ℤ)

/- Remark 64.6.5
The complex K is the bounded-below termwise-injective representative used in the
preceding derived-functor construction. -/
@[stacks 03T8] #check
  (CategoryTheory.Functor.RightDerived.Bounded.injectiveHomologyIso F K i :
    ((CochainComplex.Plus.ι B).obj (F.mapCochainComplexPlus.obj K)).homology i ≅
      (DerivedCategory.Plus.homologyFunctor B i).obj
        (F.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.Qh).obj ((HomotopyCategory.Plus.quotient A).obj K))))

end Bounded
end RightDerived
end Functor
end CategoryTheory
