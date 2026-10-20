module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Functor CategoryTheory.Pretriangulated
open ComplexShape
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Modules
variable {S : Scheme.{u}}
variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Whiskered cochain unit exhibiting `Rf_* ⋙ ((-)⟦1⟧)` as a right-derived functor. -/
def moduleDerivedPushforward_shiftWhiskerUnit :
    (pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ⋙
          shiftFunctor (ModuleDerived Y) (1 : ℤ) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        moduleDerivedPushforward f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ) :=
  whiskerRight (Functor.RightDerived.KInjective.unit.{u} (pushforward f))
    (shiftFunctor (ModuleDerived Y) (1 : ℤ))

/-- `Rf_* ⋙ ((-)⟦1⟧)` is a cochain-level right-derived model of `f_*`. -/
instance moduleDerivedPushforward_shiftWhisker_isRightDerived :
    (moduleDerivedPushforward f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ)).IsRightDerivedFunctor
      (moduleDerivedPushforward_shiftWhiskerUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- Cochain-level unit exhibiting `((-)⟦1⟧) ⋙ Rf_*` as a right-derived functor. -/
def moduleDerivedPushforward_shiftSourceUnit :
    (pushforward f).mapHomologicalComplex (up ℤ) ⋙
        shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ) ⋙
          (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ moduleDerivedPushforward f where
  app K :=
    DerivedCategory.Q.map
        (((pushforward f).mapCochainComplexShiftIso (1 : ℤ)).inv.app K) ≫
      (Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app (K⟦(1 : ℤ)⟧) ≫
      (moduleDerivedPushforward f).map
        (((DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X).commShiftIso
            (1 : ℤ)).hom.app K)
  naturality := fun _ _ _ ↦ sorry

/-- `((-)⟦1⟧) ⋙ Rf_*` is a cochain-level right-derived model of `f_*`. -/
instance moduleDerivedPushforward_shiftSource_isRightDerived :
    (shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ moduleDerivedPushforward f).IsRightDerivedFunctor
      (moduleDerivedPushforward_shiftSourceUnit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

/-- `Rf_*` commutes with the shift `[1]`. -/
def moduleDerivedPushforward_commShiftIso1 :
    shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ moduleDerivedPushforward f ≅
      moduleDerivedPushforward f ⋙ shiftFunctor (ModuleDerived Y) (1 : ℤ) :=
  Functor.RightDerived.natIsoOfIso
    (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (moduleDerivedPushforward_shiftSourceUnit f) (moduleDerivedPushforward_shiftWhiskerUnit f)
    (isoWhiskerLeft ((pushforward f).mapHomologicalComplex (up ℤ))
      ((DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y).commShiftIso
        (1 : ℤ)))


/-- Module pushforward is pointwise right derivable at every homotopy complex. -/
instance hasPointwiseRightDerivedFunctorAt_pushforward
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : HomotopyCategory X.Modules (up ℤ)) :
    (Functor.Homotopy.toDerived (Modules.pushforward f)).HasPointwiseRightDerivedFunctorAt
      (HomotopyCategory.quasiIso X.Modules (up ℤ)) K :=
  sorry

/-- Total right derived module pushforward commutes with integer shifts. -/
noncomputable instance moduleDerivedPushforward.commShift
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (moduleDerivedPushforward f).CommShift ℤ :=
  Functor.totalRightDerived_commShift
    (Functor.Homotopy.toDerived (Modules.pushforward f))
    (HomotopyCategory.quasiIso X.Modules (up ℤ)) DerivedCategory.Qh

end AlgebraicGeometry.AlgebraicSpace.Modules
