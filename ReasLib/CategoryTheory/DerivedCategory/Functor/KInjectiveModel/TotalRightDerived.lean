module
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
/-! # Specified K-injective models and supplied total right-derived functors -/
@[expose] public section
open CategoryTheory CategoryTheory.Limits ComplexShape
noncomputable section
namespace CategoryTheory.Functor.KInjectiveModel
universe w uA vA uB vB uC vC wA wB wC
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C]

/-- Both sides retain their actual universal maps: canonical K-injective models on the
left, and the caller's chosen total-derived witness on the right. -/
def totalRightDerivedIso [IsGrothendieckAbelian.{w} A]
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso A (up ℤ))] :
    KInjectiveModel.derived.{w} F ≅ RightDerived.Cochain.functor F := by
  letI hNative : (RightDerived.Cochain.functor F).IsRightDerivedFunctor (RightDerived.Cochain.unit F)
      (HomologicalComplex.quasiIso A (up ℤ)) :=
    Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit
      (RightDerived.Cochain.toDerived F) (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (up ℤ))
  exact @KInjectiveModel.isoOfModel.{w, uA, vA, uB, vB, wA, wB}
    A _ _ _ B _ _ _ _ F _ (RightDerived.Cochain.functor F)
    (RightDerived.Cochain.unit F) hNative

/-- Exact postcomposition uses the same actual source resolution before comparing each
side with the supplied total-derived functor. -/
def postcomposeTotalRightDerivedIso [IsGrothendieckAbelian.{w} A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [Functor.HasRightDerivedFunctor (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso A (up ℤ))]
    [Functor.HasRightDerivedFunctor (RightDerived.Cochain.toDerived (F ⋙ G))
      (HomologicalComplex.quasiIso A (up ℤ))] :
    RightDerived.Cochain.functor F ⋙ G.mapDerivedCategory ≅
      RightDerived.Cochain.functor (F ⋙ G) :=
  isoWhiskerRight (totalRightDerivedIso F).symm G.mapDerivedCategory ≪≫
    KInjectiveModel.postcomposeIso F G ≪≫ totalRightDerivedIso (F ⋙ G)


end CategoryTheory.Functor.KInjectiveModel
