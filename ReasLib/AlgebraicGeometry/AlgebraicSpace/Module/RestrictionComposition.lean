module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Composition and transport of étale module restriction

Restriction along a composite étale morphism is the composite of restrictions.
Equal étale morphisms induce equal restrictions of a module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- Restriction along a composite étale morphism is naturally isomorphic to
successive restriction, via the adjoint mate of pushforward composition. -/
def restrictFunctorCompIso (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) [Etale g] :
    restrictFunctor g ⋙ restrictFunctor f ≅ restrictFunctor (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (restrictAdjunction g) (restrictAdjunction f)
    (restrictAdjunction (f ≫ g)) (pushforwardComp f g)

/-- Equal étale morphisms give equal restrictions of every module. -/
theorem restrict_eq_of_hom_eq (F : Y.Modules) (f g : X ⟶ Y) [Etale f] [Etale g]
    (h : f = g) : restrict F f = restrict F g := by
  cases h
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
