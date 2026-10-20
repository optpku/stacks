module

public import ReasLib.Algebra.PolynomialTower
public import ReasLib.CategoryTheory.DerivedCategory.Functor.PresheafLowerShriek
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.InverseImage

/-!
# Derived lower shriek for polynomial squares

For each of the three projections of polynomial squares over a ring tower,
the derived inverse-image counit and the derived-colimit comparison are invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u q q1 q2 q3 t

namespace Algebra.PolynomialTower

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

variable [HasDerivedCategory.{q} (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q1} (((PolynomialOver A B)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q2} (((PolynomialOver A C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q3} (((PolynomialOver B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]

section LowerShriek

variable [∀ F : ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u},
  ((forgetToBase A B C).op).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (((forgetToBase A B C).op).op.lan :
      (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (((PolynomialOver A B)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

variable [∀ F : ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u},
  ((forgetToOverA A B C).op).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (((forgetToOverA A B C).op).op.lan :
      (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (((PolynomialOver A C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

variable [∀ F : ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u},
  ((forgetToOverB A B C).op).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (((forgetToOverB A B C).op).op.lan :
      (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (((PolynomialOver B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- The canonical derived inverse-image counit for the first projection
of polynomial squares is invertible. -/
instance u1_lowerShriek_inverseImage_isIso :
    IsIso (CategoryTheory.DerivedPresheaf.lowerShriekInverseImageCounit
      (forgetToBase A B C).op) := sorry

/-- The canonical derived inverse-image counit for the second projection
of polynomial squares is invertible. -/
instance u2_lowerShriek_inverseImage_isIso :
    IsIso (CategoryTheory.DerivedPresheaf.lowerShriekInverseImageCounit
      (forgetToOverA A B C).op) := sorry

/-- The canonical derived inverse-image counit for the tensor base-change projection
of polynomial squares is invertible. -/
instance u3_lowerShriek_inverseImage_isIso :
    IsIso (CategoryTheory.DerivedPresheaf.lowerShriekInverseImageCounit
      (forgetToOverB A B C).op) := sorry


end LowerShriek

section DerivedColimit

variable [HasDerivedCategory.{t} AddCommGrpCat.{u}]
variable [HasColimitsOfShape ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ AddCommGrpCat.{u}]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialTower A B C)ᵒᵖ AddCommGrpCat.{u} :
    HomotopyCategory (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (ComplexShape.up ℤ) ⥤ DerivedCategory.{t} AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [HasColimitsOfShape ((PolynomialOver A B)ᵒᵖ)ᵒᵖ AddCommGrpCat.{u}]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialOver A B)ᵒᵖ AddCommGrpCat.{u} :
    HomotopyCategory (((PolynomialOver A B)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (ComplexShape.up ℤ) ⥤ DerivedCategory.{t} AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso (((PolynomialOver A B)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [HasColimitsOfShape ((PolynomialOver A C)ᵒᵖ)ᵒᵖ AddCommGrpCat.{u}]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialOver A C)ᵒᵖ AddCommGrpCat.{u} :
    HomotopyCategory (((PolynomialOver A C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (ComplexShape.up ℤ) ⥤ DerivedCategory.{t} AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso (((PolynomialOver A C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]
variable [HasColimitsOfShape ((PolynomialOver B C)ᵒᵖ)ᵒᵖ AddCommGrpCat.{u}]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialOver B C)ᵒᵖ AddCommGrpCat.{u} :
    HomotopyCategory (((PolynomialOver B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
      (ComplexShape.up ℤ) ⥤ DerivedCategory.{t} AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso (((PolynomialOver B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/-- The canonical derived-colimit comparison for the first projection
of polynomial squares is invertible. -/
instance u1_inverseImageComparison_isIso :
    IsIso (CategoryTheory.DerivedColimit.inverseImageComparison AddCommGrpCat.{u}
      (forgetToBase A B C).op) := sorry

/-- The canonical derived-colimit comparison for the second projection
of polynomial squares is invertible. -/
instance u2_inverseImageComparison_isIso :
    IsIso (CategoryTheory.DerivedColimit.inverseImageComparison AddCommGrpCat.{u}
      (forgetToOverA A B C).op) := sorry

/-- The canonical derived-colimit comparison for the tensor base-change projection
of polynomial squares is invertible. -/
instance u3_inverseImageComparison_isIso :
    IsIso (CategoryTheory.DerivedColimit.inverseImageComparison AddCommGrpCat.{u}
      (forgetToOverB A B C).op) := sorry

end DerivedColimit

end Algebra.PolynomialTower
