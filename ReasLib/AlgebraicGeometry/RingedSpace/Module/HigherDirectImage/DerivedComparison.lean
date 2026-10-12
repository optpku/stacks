/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Cohomology.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution

/-! # Ordinary and derived higher direct images -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage

/-- The ordinary right-derived degree agrees naturally with the cohomology of the
unbounded derived pushforward of a single module. The comparison uses the chosen
injective-resolution computation and the canonical bounded/unbounded comparison. -/
def derivedCohomologyNatIso {X Y : RingedSpace.{u}} (f : X ⟶ Y) (n : ℕ) :
    higherDirectImageModuleFunctor f n ≅
      DerivedCategory.singleFunctor X.Modules 0 ⋙ moduleDerivedPushforward f ⋙
        DerivedCategory.homologyFunctor Y.Modules (n : ℤ) :=
  (Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
      (pushforward f) n).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor X.Modules 0)
        (Functor.RightDerived.Homotopy.BoundedBelow.canonicalModelIso (pushforward f)))
      (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso X.Modules 0)
      (moduleDerivedPushforward f ⋙ DerivedCategory.homologyFunctor Y.Modules (n : ℤ))

/-- The component of the canonical ordinary/derived comparison. -/
def derivedCohomologyIso {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (F : X.Modules) (n : ℕ) :
    higherDirectImageModule f F n ≅
      (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).obj
        ((moduleDerivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
  (derivedCohomologyNatIso f n).app F

/-- Naturality of the ordinary/derived comparison in the coefficient module. -/
@[reassoc]
theorem derivedCohomologyIso_hom_naturality {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    {F G : X.Modules} (a : F ⟶ G) (n : ℕ) :
    higherDirectImageModuleMap f a n ≫ (derivedCohomologyIso f G n).hom =
      (derivedCohomologyIso f F n).hom ≫
        (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
          ((moduleDerivedPushforward f).map ((DerivedCategory.singleFunctor X.Modules 0).map a)) :=
  (derivedCohomologyNatIso f n).hom.naturality a

end AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage
