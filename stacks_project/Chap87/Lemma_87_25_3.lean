module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective.BaseChange
import StacksCheckRecall

/-!
# Base change of surjective morphisms of formal algebraic spaces

A base change of a surjective morphism of formal algebraic spaces is again
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

open AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.25.3: A base change of a surjective morphism of formal algebraic
spaces is a surjective morphism. -/
@[stacks 0GHR] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.Surjective.of_isPullback :
    ∀ {S : Scheme.{u}}
    {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Y'] [IsFormalAlgebraicSpace B],
    (RX : ReductionData X) → (RY : ReductionData Y) →
    (RY' : ReductionData Y') → (RB : ReductionData B) →
    ∀
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f),
    ReductionData.Surjective RY RB g → ReductionData.Surjective RY' RX g')

#check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.Surjective.pullback_snd :
    ∀ {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z],
    (RX : ReductionData X) → (RY : ReductionData Y) → (RZ : ReductionData Z) →
    ∀
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)],
    (RP : ReductionData (pullback f g)) →
    ReductionData.Surjective RX RY f → ReductionData.Surjective RP RZ (pullback.snd f g))
