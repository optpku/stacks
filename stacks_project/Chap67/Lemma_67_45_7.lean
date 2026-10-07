module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Integral morphisms of algebraic spaces versus affine universally closed morphisms

A morphism of algebraic spaces is integral if and only if it is affine and
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Affine

/-- An integral morphism of algebraic spaces is affine. -/
instance of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] : Affine f :=
  sorry

end Affine

namespace UniversallyClosed

/-- An integral morphism of algebraic spaces is universally closed. -/
instance of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] : UniversallyClosed f :=
  sorry

end UniversallyClosed

namespace IsIntegralHom

/-- An affine and universally closed morphism of algebraic spaces is integral. -/
theorem of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] [UniversallyClosed f] : IsIntegralHom f :=
  sorry

/-- Lemma 67.45.7: A morphism of algebraic spaces is integral if and only if it
is affine and universally closed. -/
@[stacks 0415]
theorem iff_universallyClosed_and_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsIntegralHom f ↔ UniversallyClosed f ∧ Affine f :=
  sorry

/-- The morphism property of being an integral morphism of algebraic spaces
equals the infimum of being universally closed and affine. -/
theorem eq_universallyClosed_inf_affine {S : Scheme.{u}} :
    (@IsIntegralHom S : MorphismProperty (AlgebraicSpace S)) =
      (@UniversallyClosed S ⊓ @Affine S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end IsIntegralHom

end AlgebraicGeometry.AlgebraicSpace
