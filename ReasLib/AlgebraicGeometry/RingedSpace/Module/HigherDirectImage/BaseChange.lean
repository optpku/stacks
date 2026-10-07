module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.DerivedComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback.Truncation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction.Opens
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange

/-! # Canonical higher-direct-image base change

The comparison is built in every degree from ordinary/derived comparison,
functorial upper truncation, the derived base-change mate, and the coefficient
counit. Arbitrary base change is retained throughout.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- The canonical derived mate for a commutative square of ringed spaces, using
the canonical absolute-derived adjunctions and composition comparisons. -/
def higherDirectImageDerivedBaseChange
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) :
    DerivedBaseChange.source f g ⟶ DerivedBaseChange.target g' f' :=
  DerivedBaseChange.map
    (modulePullbackDerivedPushforwardAdjunction f)
    (modulePullbackDerivedPushforwardAdjunction f')
    (DerivedBaseChange.pullbackIsoOfIsIso sq
      (modulePullbackDerived.compComparison_isIso f' g)
      (modulePullbackDerived.compComparison_isIso g' f))

/-- Higher-direct-image base change as a natural transformation in the coefficient
module. Every factor is a specified natural transformation or natural isomorphism. -/
def higherDirectImageModuleBaseChangeNatTrans
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) (n : ℕ) :
    higherDirectImageModuleFunctor f n ⋙ pullback g ⟶
      pullback g' ⋙ higherDirectImageModuleFunctor f' n :=
  (Functor.isoWhiskerRight (HigherDirectImage.derivedCohomologyNatIso f n)
      (pullback g)).hom ≫
    Functor.whiskerLeft (DerivedCategory.singleFunctor X.Modules 0 ⋙ moduleDerivedPushforward f)
      (pullbackComparisonNatTrans g (n : ℤ)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (DerivedCategory.singleFunctor X.Modules 0)
        (higherDirectImageDerivedBaseChange sq))
      (DerivedCategory.homologyFunctor S'.Modules (n : ℤ)) ≫
    Functor.whiskerRight (singlePullbackComparisonNatTrans g' 0)
      (moduleDerivedPushforward f' ⋙ DerivedCategory.homologyFunctor S'.Modules (n : ℤ)) ≫
    (Functor.isoWhiskerLeft (pullback g')
      (HigherDirectImage.derivedCohomologyNatIso f' n).symm).hom

/-- The canonical base-change morphism for an arbitrary commutative square,
coefficient module and natural degree. -/
def higherDirectImageModuleBaseChangeMap
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) (F : X.Modules) (n : ℕ) :
    (pullback g).obj (higherDirectImageModule f F n) ⟶
      higherDirectImageModule f' ((pullback g').obj F) n :=
  (higherDirectImageModuleBaseChangeNatTrans sq n).app F

/-- Naturality of the canonical comparison in the coefficient module. -/
@[reassoc]
theorem higherDirectImageModuleBaseChangeMap_naturality
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) {F G : X.Modules} (a : F ⟶ G) (n : ℕ) :
    (pullback g).map (higherDirectImageModuleMap f a n) ≫
        higherDirectImageModuleBaseChangeMap sq G n =
      higherDirectImageModuleBaseChangeMap sq F n ≫
        higherDirectImageModuleMap f' ((pullback g').map a) n :=
  (higherDirectImageModuleBaseChangeNatTrans sq n).naturality a

/-- The canonical comparison is the composite of the ordinary/derived comparison,
the cohomology edge map, the derived mate, and the single-module counit. -/
theorem higherDirectImageModuleBaseChangeMap_factorization
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) (F : X.Modules) (n : ℕ) :
    higherDirectImageModuleBaseChangeMap sq F n =
      (pullback g).map (HigherDirectImage.derivedCohomologyIso f F n).hom ≫
        pullbackComparison g ((moduleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) (n : ℤ) ≫
        (DerivedCategory.homologyFunctor S'.Modules (n : ℤ)).map
          ((higherDirectImageDerivedBaseChange sq).app
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
        (DerivedCategory.homologyFunctor S'.Modules (n : ℤ)).map
          ((moduleDerivedPushforward f').map (singlePullbackComparison g' F 0)) ≫
        (HigherDirectImage.derivedCohomologyIso f' ((pullback g').obj F) n).inv := rfl

/-- In degree zero the construction recovers the underived base-change mate,
after the canonical zeroth-right-derived identifications. -/
theorem higherDirectImageModuleBaseChangeMap_zero
    {X X' S S' : RingedSpace.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : CommSq g' f' f g) (F : X.Modules) :
    higherDirectImageModuleBaseChangeMap sq F 0 ≫
        (pushforward f').rightDerivedZeroIsoSelf.hom.app ((pullback g').obj F) =
      (pullback g).map ((pushforward f).rightDerivedZeroIsoSelf.hom.app F) ≫
        (BaseChange.map sq).app F := sorry

end AlgebraicGeometry.RingedSpace.Hom
