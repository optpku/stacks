module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded

/-! # Derived étale restriction–pushforward adjunction

Étale restriction and K-injective derived pushforward form an adjunction on
unbounded derived categories of modules on algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {V X : AlgebraicSpace S}

/-- The unbounded derived adjunction `f^* ⊣ Rf_*` associated to an étale morphism of
algebraic spaces. -/
def restrictPushforwardDerivedAdjunction (f : V ⟶ X) [Etale f] :
    restrictFunctorDerived f ⊣ moduleDerivedPushforward f :=
  Adjunction.Derived.KInjective.adjunction
    (ExactFunctor.of (restrictFunctor f)) (pushforward f) (restrictAdjunction f)

end AlgebraicGeometry.AlgebraicSpace.Modules
