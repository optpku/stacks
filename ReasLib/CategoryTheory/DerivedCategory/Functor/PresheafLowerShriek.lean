module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity

/-!
# Derived lower shriek on abelian presheaves

The counit of left Kan extension and precomposition induces a canonical
comparison from inverse image followed by derived lower shriek to the identity.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u uC uC' v v' q q'

namespace CategoryTheory

variable {C : Type uC} [Category.{v} C]
variable {C' : Type uC'} [Category.{v'} C']
variable (u : C' ⥤ C)
variable [∀ F : C'ᵒᵖ ⥤ AddCommGrpCat.{u}, u.op.HasLeftKanExtension F]

/-- Left Kan extension on abelian-group-valued presheaves is additive. -/
instance Functor.presheafLan_additive :
    (u.op.lan :
      (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).Additive :=
  (u.op.lanAdjunction AddCommGrpCat.{u}).left_adjoint_additive

namespace DerivedPresheaf

variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q'} (C'ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (u.op.lan : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- The canonical derived counit from inverse image followed by derived left Kan
extension to the identity on the target presheaf derived category. -/
def lowerShriekInverseImageCounit :
    (Functor.presheafInverseImage u AddCommGrpCat.{u}).mapDerivedCategory ⋙
        Functor.LeftDerived.Homotopy.functor
          (u.op.lan : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})) ⟶
      𝟭 (DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u})) :=
  Functor.LeftDerived.Homotopy.Composition.ExactFirst.comparison
      (Functor.presheafInverseImageExact AddCommGrpCat.{u} u)
      u.op.lan (ExactFunctor.id (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
      (u.op.lanAdjunction AddCommGrpCat.{u}).counit ≫
    (ExactFunctor.MapDerivedCategory.idFunctorIso (Cᵒᵖ ⥤ AddCommGrpCat.{u})).hom

/-- Precomposing the derived counit with homotopy localization recovers the
comparison induced by the left Kan extension counit and the derived identity. -/
theorem lowerShriekInverseImageCounit_fac :
    Functor.whiskerLeft
        (DerivedCategory.Qh :
          HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
            DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
        (lowerShriekInverseImageCounit u) =
      Functor.LeftDerived.Homotopy.Composition.ExactFirst.comparisonOnHomotopy
          (Functor.presheafInverseImageExact AddCommGrpCat.{u} u)
          u.op.lan (ExactFunctor.id (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
          (u.op.lanAdjunction AddCommGrpCat.{u}).counit ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
              DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
          (ExactFunctor.MapDerivedCategory.idFunctorIso (Cᵒᵖ ⥤ AddCommGrpCat.{u})).hom := by
  rw [lowerShriekInverseImageCounit, Functor.whiskerLeft_comp]
  exact congrArg (fun τ ↦ τ ≫ _)
    (Functor.LeftDerived.Homotopy.Composition.ExactFirst.comparison_fac
      (Functor.presheafInverseImageExact AddCommGrpCat.{u} u)
      u.op.lan (ExactFunctor.id (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
      (u.op.lanAdjunction AddCommGrpCat.{u}).counit)

end DerivedPresheaf

end CategoryTheory
