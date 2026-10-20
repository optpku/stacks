/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyClosed

/-!
# Integral morphisms of algebraic spaces

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

/-- A morphism of algebraic spaces is integral if and only if it is affine and
universally closed. -/
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
