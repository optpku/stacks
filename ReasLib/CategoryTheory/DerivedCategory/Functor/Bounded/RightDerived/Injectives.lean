module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

noncomputable section

universe vA vB uA uB

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [EnoughInjectives A]

/-- The unit of the bounded-below right-derived functor is invertible on injective complexes. -/
@[stacks 03T7]
theorem rightDerivedFunctorPlusUnit_isIso_on_injectives
    (X : HomotopyCategory.Plus (InjectiveObject A)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X)) := by
  infer_instance

end CategoryTheory.Functor

end
