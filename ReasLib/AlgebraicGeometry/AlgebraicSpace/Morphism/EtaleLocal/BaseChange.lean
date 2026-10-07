module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale-local lift of a scheme-morphism property that is stable under
base change is stable under base change for algebraic spaces. -/
instance etaleLocal_isStableUnderBaseChange {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] :
    (etaleLocal P : MorphismProperty (AlgebraicSpace S)).IsStableUnderBaseChange :=
  sorry

/-- Pulling back a morphism of algebraic spaces with the étale-local lift of a
base-change-stable scheme-morphism property preserves that lifted property. -/
theorem etaleLocal.of_isPullback {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderBaseChange]
    {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : etaleLocal P g) :
    etaleLocal P g' :=
  sorry

/-- The second projection from a pullback of a morphism with the étale-local
lift of a base-change-stable scheme-morphism property has that lifted property. -/
theorem etaleLocal.pullback_snd {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderBaseChange]
    {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} (hf : etaleLocal P f) (g : Z ⟶ Y)
    [HasPullback f g] : etaleLocal P (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
