module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Stability properties of étale morphisms
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Etale

/-- In a pullback square, the pullback of an étale morphism is étale. -/
theorem of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : Y' ⟶ X} {f' : Y' ⟶ Y} (sq : IsPullback i f' f g) [Etale f] :
    Etale f' := sorry

/-- The composite of two étale scheme morphisms is étale. -/
theorem comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) := sorry

/-- The first projection from a pullback of an étale morphism is étale. -/
theorem pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [Etale g] : Etale (pullback.fst f g) := sorry

end AlgebraicGeometry.Etale
