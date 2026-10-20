module

public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The property of a scheme morphism whose target is locally Noetherian. -/
def LocallyNoetherianTarget : MorphismProperty Scheme.{u} :=
  MorphismProperty.ofObjectProperty ⊤
    (IsLocallyNoetherian : ObjectProperty Scheme.{u})

namespace LocallyNoetherianTarget

/-- A scheme morphism has locally Noetherian target exactly when its target is locally
Noetherian. -/
theorem iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyNoetherianTarget f ↔ IsLocallyNoetherian Y := sorry

/-- Precomposition does not change whether a scheme morphism has locally Noetherian target. -/
theorem precomp_iff {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) :
    LocallyNoetherianTarget (g ≫ f) ↔ LocallyNoetherianTarget f := sorry

/-- Having locally Noetherian target is local at the target for the étale precoverage. -/
instance instIsLocalAtTargetEtale :
    LocallyNoetherianTarget.IsLocalAtTarget Scheme.etalePrecoverage := sorry

end LocallyNoetherianTarget

end AlgebraicGeometry
