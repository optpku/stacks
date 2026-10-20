module

public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.LeftExactAdjunction

/-- The canonical left-exact adjunction from the slice over an object of a finite-limit
Cartesian closed category to the category itself has inverse image `Over.star object` and
direct image `Over.sections object`. -/
noncomputable def sheafLocalization
    {Base : Type u} [Category.{v} Base] [HasFiniteLimits Base]
    [CartesianMonoidalCategory Base] [MonoidalClosed Base] [BraidedCategory Base]
    (object : Base) [ChosenPullbacksAlong (curryRightUnitorHom object)] :
    LeftExactAdjunction (Over object) Base where
  inverseImageFunctor :=
    { obj := Over.star object
      property := (inferInstance : PreservesFiniteLimits (Over.star object)) }
  pushforward := Over.sections object
  adjunction := (Over.toOverSectionsAdj object).ofNatIsoLeft
    ((Over.forgetAdjStar object).rightAdjointUniq (forgetAdjToOver object)).symm

end CategoryTheory.LeftExactAdjunction
