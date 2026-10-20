module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total Left Derived Functors of Preadditive-Source Composites

This leaf derives the homotopy-to-derived composite of two additive functors.
The intermediate category need only be preadditive; only the source and final
target need derived-category structure.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA uB vB uC vC

namespace CategoryTheory.Functor

section

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]

namespace Homotopy.LeftDerived

/-- The total left derived functor of a composable pair of additive functors, formed from its
generic homotopy-to-derived composite. -/
@[stacks 05S3 "total derived functor of a composite",
  stacks 0FTG "total left-derived functor of a two-stage construction"]
noncomputable def total (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive]
    [HasLeftDerivedFunctor (Homotopy.Comp.toDerived F G)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    DerivedCategory A ⥤ DerivedCategory C :=
  (Homotopy.Comp.toDerived F G).totalLeftDerived
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- Unfolding `total` gives the total left derived functor of the corresponding
homotopy-to-derived composite. -/
@[stacks 05S3 "total derived functor of a composite"]
theorem total_def (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive]
    [HasLeftDerivedFunctor (Homotopy.Comp.toDerived F G)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    total F G =
      (Homotopy.Comp.toDerived F G).totalLeftDerived
        (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
        (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- The canonical counit of `total`. -/
@[stacks 05S3 "total derived functor of a composite"]
noncomputable def counit (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive]
    [HasLeftDerivedFunctor (Homotopy.Comp.toDerived F G)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ total F G ⟶
      Homotopy.Comp.toDerived F G :=
  (Homotopy.Comp.toDerived F G).totalLeftDerivedCounit
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- The derived counit of `total` has the expected source and target. -/
@[stacks 05S3 "total derived functor of a composite"]
theorem counit_def (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive]
    [HasLeftDerivedFunctor (Homotopy.Comp.toDerived F G)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    counit F G =
      (Homotopy.Comp.toDerived F G).totalLeftDerivedCounit
        (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
        (HomotopyCategory.quasiIso A (up ℤ)) := sorry

end Homotopy.LeftDerived

end

end CategoryTheory.Functor
