module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Unramified morphisms are étale local on the source

Unramifiedness of morphisms of algebraic spaces is local on the source for the
étale precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Unramified

/-- Unramifiedness of morphisms of algebraic spaces is local on the source for
the étale precoverage. -/
instance isLocalAtSourceEtale {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Unramified S : MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is unramified if and only if it remains so
after precomposition with every member of an étale covering of the source. -/
theorem iff_forall_comp_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (@etalePrecoverage S).ZeroHypercover X) :
    Unramified f ↔ ∀ i, Unramified (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Unramified
