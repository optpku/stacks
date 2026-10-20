module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Tor-independent derived base change on algebraic spaces

A commutative square of algebraic spaces induces the unbounded derived mate
`Lg^* Rf_* ⟶ Rf'_* L(g')^*`. When the square is cartesian, `f` is quasi-compact
and quasi-separated, and `X` and `Y'` are Tor independent over `Y`, every
component of this mate on `D_QCoh(𝒪_X)` is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived.compIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X),
    modulePullbackDerived g ⋙ modulePullbackDerived f ≅ modulePullbackDerived (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived.compComparison :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X),
    modulePullbackDerived g ⋙ modulePullbackDerived f ⟶ modulePullbackDerived (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived.compComparison_isIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X),
    IsIso (modulePullbackDerived.compComparison f g))

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived.compComparison_eq :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X),
    modulePullbackDerived.compComparison f g =
      Functor.LeftDerived.Homotopy.Composition.comparison
        (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
        (Modules.pullbackCompIso f g).symm)

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange

#check (source :
  ∀ {S : Scheme.{u}} {X Y' Y : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
    ModuleDerived X ⥤ ModuleDerived Y')

#check (target :
  ∀ {S : Scheme.{u}} {X' X Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y'),
    ModuleDerived X ⥤ ModuleDerived Y')

#check (pullbackCartesianIso :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
    CommSq g' f' f g →
      (modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived g'))

#check (pullbackCartesianIso_hom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g),
    (pullbackCartesianIso sq).hom =
      ModuleDerived.totalPullbackCompComparison f' g ≫
        eqToHom (congrArg (fun h : X' ⟶ Y ↦
          Functor.LeftDerived.Homotopy.functor (Modules.pullback h)) sq.w.symm) ≫
          inv (ModuleDerived.totalPullbackCompComparison g' f))

#check (map :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y},
    CommSq g' f' f g → (source f g ⟶ target g' f'))

#check (app :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (E : ModuleDerived X),
    (source f g).obj E ⟶ (target g' f').obj E)

#check (map_spec :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (E : ModuleDerived X),
    ((modulePullbackDerivedPushforwardAdjunction f').homEquiv
        ((source f g).obj E) ((modulePullbackDerived g').obj E)).symm (app sq E) =
      (pullbackCartesianIso sq).hom.app ((Modules.pushforwardDerived f).obj E) ≫
        (modulePullbackDerived g').map
          ((modulePullbackDerivedPushforwardAdjunction f).counit.app E))

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedBaseChange

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange

#check (map_app_isIso :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (sq : IsPullback g' f' f g),
    TorIndependentOver (Over.mk f) (Over.mk g) → ∀ (E : DerivedQCoh X),
      IsIso ((Hom.DerivedBaseChange.map sq.toCommSq).app E.obj))

end AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange

