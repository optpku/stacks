module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap73.Definition_73_4_1_Precoverage

/-!
# Smooth morphisms are smooth local on the source

Smoothness of morphisms of algebraic spaces is local on the source for the
smooth precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- Smoothness of morphisms of algebraic spaces is local on the source for the
smooth precoverage. -/
instance isLocalAtSourceSmooth {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Smooth S)) :=
  sorry

/-- A morphism of algebraic spaces is smooth if and only if it remains so after
precomposition with every member of a smooth covering of the source. -/
theorem iff_forall_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (precoverage (@Smooth S)).ZeroHypercover X) :
    Smooth f ↔ ∀ i, Smooth (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
