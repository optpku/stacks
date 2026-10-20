module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit

/-!
# Derived colimits over a point

This leaf specializes the generic derived-colimit API to presheaf categories.
It owns the reusable notation and explicit functors for the projection from
`Cᵒᵖ ⥤ A` to a point.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory

/-- The homotopy-to-derived functor induced by the projection from `A`-valued presheaves on
`C` to a point. -/
abbrev categoryOverPointColimitToDerived
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A] :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  Functor.colimitToDerived Cᵒᵖ A

/-- The total left derived colimit induced by the projection from `A`-valued presheaves on
`C` to a point. -/
abbrev categoryOverPointDerivedColimit
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  Functor.derivedColimit Cᵒᵖ A

/-- An explicit model for the derived colimit over a category over a point. -/
@[stacks 05SA "explicit derived colimit over a point model"]
abbrev CategoryOverPointModel
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A] :=
  Functor.ColimitModel Cᵒᵖ A

/-- The canonical explicit point-colimit model obtained from a left-derived-functor instance. -/
@[stacks 05SA "canonical derived colimit over a point model"]
noncomputable def categoryOverPointDerivedColimitModel
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    CategoryOverPointModel C A :=
  Functor.derivedColimitModel Cᵒᵖ A

/-- Any explicit point-colimit model is canonically identified with the total derived colimit. -/
@[stacks 05SA "explicit point-colimit model comparison"]
noncomputable def CategoryOverPointModel.isoDerivedColimit
    (C : Type u) [Category.{v} C] (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)] [HasColimitsOfShape Cᵒᵖ A]
    (M : CategoryOverPointModel C A)
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    M.functor ≅ categoryOverPointDerivedColimit C A :=
  Functor.ColimitModel.isoDerivedColimit Cᵒᵖ A M

/- Lean surface notation for the recurring derived lower shriek `Lπ!` attached to the projection
from a category over a point. -/
scoped notation:max "Lπ![" C:max ", " A:max "]" => categoryOverPointDerivedColimit C A

end CategoryTheory
