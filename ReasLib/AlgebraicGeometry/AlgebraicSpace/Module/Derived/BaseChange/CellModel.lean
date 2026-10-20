module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-! # Derived base change on native module cell models -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ModuleDerived

/-- The canonical derived identification of the two paths around a cartesian square,
built from composition comparisons and the square equality `g' ≫ f = f' ≫ g`. -/
noncomputable def pullbackCartesianIso {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)] :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  asIso (pullbackCompComparison f' g) ≪≫
    eqToIso (congrArg pullback sq.w.symm) ≪≫
    (asIso (pullbackCompComparison g' f)).symm

/-- The cartesian derived identification is the composition comparison along `f' ≫ g`,
the equality `sq.w`, and the inverse composition comparison along `g' ≫ f`. -/
theorem pullbackCartesianIso_hom {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [IsIso (pullbackCompComparison f' g)] [IsIso (pullbackCompComparison g' f)] :
    (pullbackCartesianIso g' f' f g sq).hom =
      pullbackCompComparison f' g ≫
        eqToHom (congrArg pullback sq.w.symm) ≫ inv (pullbackCompComparison g' f) := sorry

end ModuleDerived

/-- The derived base-change mate `β : L(g)^* Rf_* ω ⟶ Rf'_* L(g')^* ω` of a cartesian
square. -/
noncomputable def baseChangeMate {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (ω : ModuleDerived X) :
    (ModuleDerived.pullback g).obj ((moduleDerivedPushforward f).obj ω) ⟶
      (moduleDerivedPushforward f').obj ((ModuleDerived.pullback g').obj ω) :=
  (CategoryTheory.DerivedBaseChange.map adj_f adj_f'
      (ModuleDerived.pullbackCartesianIso g' f' f g sq)).app ω

/-- The base-change mate is the component of the categorical right mate at `ω`. -/
theorem baseChangeMate_eq {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    (ω : ModuleDerived X) :
    baseChangeMate g' f' f g sq adj_f adj_f' ω =
      (CategoryTheory.DerivedBaseChange.map adj_f adj_f'
          (ModuleDerived.pullbackCartesianIso g' f' f g sq)).app ω := sorry

namespace ModuleDerived

/-- The canonical derived base-change component on the native pullback presentation. -/
noncomputable def baseChangeMap {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (ω : ModuleDerived X) :
    (pullback g).obj ((moduleDerivedPushforward f).obj ω) ⟶
      (moduleDerivedPushforward f').obj ((pullback g').obj ω) :=
  (pullbackIsoTotalLeftDerived g).hom.app ((moduleDerivedPushforward f).obj ω) ≫
    (Hom.DerivedBaseChange.map sq.toCommSq).app ω ≫
      (moduleDerivedPushforward f').map ((pullbackIsoTotalLeftDerived g').inv.app ω)

/-- Transporting canonical derived adjunctions to native pullback identifies their mate
with the canonical derived base-change component. -/
theorem baseChangeMap_eq_mate {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (ω : ModuleDerived X) :
    baseChangeMap g' f' f g sq ω =
      baseChangeMate g' f' f g sq
        ((Modules.derivedPullbackPushforwardAdjunction f).ofNatIsoLeft
          (pullbackIsoTotalLeftDerived f).symm)
        ((Modules.derivedPullbackPushforwardAdjunction f').ofNatIsoLeft
          (pullbackIsoTotalLeftDerived f').symm) ω := sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
