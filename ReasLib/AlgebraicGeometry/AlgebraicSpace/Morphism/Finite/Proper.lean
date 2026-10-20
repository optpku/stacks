/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Finite morphisms of algebraic spaces versus affine proper morphisms

A morphism of algebraic spaces is finite if and only if it is affine and proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsFinite

/-- A morphism of algebraic spaces is finite if and only if it is proper and affine. -/
theorem iff_proper_and_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsFinite f ↔ Proper f ∧ Affine f :=
  sorry

end IsFinite

namespace Affine

/-- A finite morphism of algebraic spaces is affine. -/
instance of_isFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : IsFinite f] : Affine f :=
  ((IsFinite.iff_proper_and_affine f).mp h).2

end Affine

namespace Proper

/-- A finite morphism of algebraic spaces is proper. -/
instance of_isFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : IsFinite f] : Proper f :=
  ((IsFinite.iff_proper_and_affine f).mp h).1

end Proper

namespace IsFinite

/-- An affine and proper morphism of algebraic spaces is finite. -/
instance (priority := 100) of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [hAffine : Affine f] [hProper : Proper f] : IsFinite f :=
  (iff_proper_and_affine f).mpr ⟨hProper, hAffine⟩

/-- The morphism property of being a finite morphism of algebraic spaces
equals the infimum of being proper and affine. -/
theorem eq_proper_inf_affine {S : Scheme.{u}} :
    (@IsFinite S : MorphismProperty (AlgebraicSpace S)) =
      (@Proper S ⊓ @Affine S : MorphismProperty (AlgebraicSpace S)) := by
  funext X Y f
  exact propext (iff_proper_and_affine f)

end IsFinite

end AlgebraicGeometry.AlgebraicSpace
