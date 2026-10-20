module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import Mathlib.CategoryTheory.Sites.Continuous

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [Ring Λ]

/-- Underived composition of small-étale module pushforwards along a pair of
scheme morphisms. -/
def etaleModulePushforwardCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModulePushforward f Λ ⋙ etaleModulePushforward g Λ ≅
      etaleModulePushforward (f ≫ g) Λ :=
  sheafPushforwardContinuousComp' (smallEtalePullbackCompIso f g)
    (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology
    X.smallEtaleTopology

end AlgebraicGeometry.Scheme.Etale

end
