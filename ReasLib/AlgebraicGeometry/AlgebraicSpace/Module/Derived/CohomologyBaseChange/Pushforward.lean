module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Equality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-! # Cohomology and derived pushforward base change on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The derived pullbacks around a cartesian square are canonically isomorphic via
the composition comparisons and the equality `g' ≫ f = f' ≫ g`. -/
def cohomologyBaseChangeCartesianIso
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) :
    ModuleDerived.pullback g ⋙ ModuleDerived.pullback f' ≅
      ModuleDerived.pullback f ⋙ ModuleDerived.pullback g' :=
  ModuleDerived.pullbackCompIso f' g ≪≫
    ModuleDerived.pullbackCongr sq.w.symm ≪≫
    (ModuleDerived.pullbackCompIso g' f).symm

/-- The cartesian derived identification is the forward composition comparison,
the square-equality transport, and the inverse composition comparison. -/
theorem cohomologyBaseChangeCartesianIso_hom
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) :
    (cohomologyBaseChangeCartesianIso sq).hom =
      ModuleDerived.pullbackCompComparison f' g ≫
        (ModuleDerived.pullbackCongr sq.w.symm).hom ≫
          inv (ModuleDerived.pullbackCompComparison g' f) := sorry

/-- The canonical derived base-change mate `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`
followed by the derived pushforward of a comparison morphism to `K'`. -/
def cohomologyBaseChangeComp (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    (Modules.moduleDerivedPushforward f ⋙ ModuleDerived.pullback g).obj ((inclusion X).obj K) ⟶
      (Modules.moduleDerivedPushforward f').obj ((inclusion X').obj K') :=
  (DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
      (derivedPullbackPushforwardAdjunction f') (cohomologyBaseChangeCartesianIso sq)).app
        ((inclusion X).obj K) ≫
    (Modules.moduleDerivedPushforward f').map α

/-- The base-change composite is the derived mate followed by the pushed-forward
comparison morphism. -/
theorem cohomologyBaseChangeComp_eq (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeComp g' f' f g sq K K' α =
      (DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction f') (cohomologyBaseChangeCartesianIso sq)).app
            ((inclusion X).obj K) ≫
        (Modules.moduleDerivedPushforward f').map α := sorry

/-- For a cartesian square of algebraic spaces, pointwise cohomology base change for
a comparison of derived quasi-coherent complexes makes the canonical derived
pushforward base-change composite invertible when `f` is quasi-compact and quasi-separated. -/
theorem cohomologyBaseChange_comp_isIso (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (h : cohomologyBaseChangeHolds sq K K' α) :
    IsIso (cohomologyBaseChangeComp g' f' f g sq K K' α) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
