module

import ReasLib.Algebra.PolynomialTower.DerivedLowerShriek
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Algebra

noncomputable section

universe u q q1 q2 q3 t

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

variable [HasDerivedCategory.{q} (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q1} (((PolynomialOver A B)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q2} (((PolynomialOver A C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [HasDerivedCategory.{q3} (((PolynomialOver B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})]

section LowerShriek

variable [∀ F : ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u},
  ((Algebra.PolynomialTower.forgetToBase A B C).op).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (((Algebra.PolynomialTower.forgetToBase A B C).op).op.lan :
      (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (((PolynomialOver A B)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

variable [∀ F : ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u},
  ((Algebra.PolynomialTower.forgetToOverA A B C).op).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (((Algebra.PolynomialTower.forgetToOverA A B C).op).op.lan :
      (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (((PolynomialOver A C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

variable [∀ F : ((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u},
  ((Algebra.PolynomialTower.forgetToOverB A B C).op).op.HasLeftKanExtension F]
variable [Functor.HasLeftDerivedFunctor
  (Functor.Homotopy.toDerived
    (((Algebra.PolynomialTower.forgetToOverB A B C).op).op.lan :
      (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (((PolynomialOver B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})))
  (HomotopyCategory.quasiIso (((PolynomialTower A B C)ᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/- Lemma 92.7.3. The canonical derived counits and derived-colimit comparisons
are invertible for all three projections of polynomial squares. -/
@[stacks 08QW]
#check (Algebra.PolynomialTower.u1_lowerShriek_inverseImage_isIso A B C :
  IsIso (CategoryTheory.DerivedPresheaf.lowerShriekInverseImageCounit
      (Algebra.PolynomialTower.forgetToBase A B C).op))

#check (Algebra.PolynomialTower.u2_lowerShriek_inverseImage_isIso A B C :
  IsIso (CategoryTheory.DerivedPresheaf.lowerShriekInverseImageCounit
      (Algebra.PolynomialTower.forgetToOverA A B C).op))

#check (Algebra.PolynomialTower.u3_lowerShriek_inverseImage_isIso A B C :
  IsIso (CategoryTheory.DerivedPresheaf.lowerShriekInverseImageCounit
      (Algebra.PolynomialTower.forgetToOverB A B C).op))


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

#check (Algebra.PolynomialTower.u1_inverseImageComparison_isIso A B C :
  IsIso (CategoryTheory.DerivedColimit.inverseImageComparison AddCommGrpCat.{u}
      (Algebra.PolynomialTower.forgetToBase A B C).op))

#check (Algebra.PolynomialTower.u2_inverseImageComparison_isIso A B C :
  IsIso (CategoryTheory.DerivedColimit.inverseImageComparison AddCommGrpCat.{u}
      (Algebra.PolynomialTower.forgetToOverA A B C).op))

#check (Algebra.PolynomialTower.u3_inverseImageComparison_isIso A B C :
  IsIso (CategoryTheory.DerivedColimit.inverseImageComparison AddCommGrpCat.{u}
      (Algebra.PolynomialTower.forgetToOverB A B C).op))

end DerivedColimit
