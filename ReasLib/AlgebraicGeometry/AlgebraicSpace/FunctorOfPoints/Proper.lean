/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Representability

/-!
# Proper relative functors of points

A relative functor of points is proper when it is represented by a proper
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A functor on `(Sch/B)ᵒᵖ` is represented by an algebraic space proper over `B`. -/
def IsProperOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (X : AlgebraicSpace S) (π : X ⟶ B), Proper π ∧ Nonempty (F ≅ yonedaOver π)

/-- Proper representability is the existence of a proper morphism `π` and an
isomorphism to its relative functor of points. -/
theorem isProperOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsProperOver F ↔
      ∃ (X : AlgebraicSpace S) (π : X ⟶ B),
        Proper π ∧ Nonempty (F ≅ yonedaOver π) := sorry

/-- A proper morphism and a representing isomorphism exhibit a functor as proper. -/
theorem IsProperOver.of {X : AlgebraicSpace S} {π : X ⟶ B} (hProper : Proper π)
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ yonedaOver π) :
    IsProperOver F := sorry

end AlgebraicGeometry.AlgebraicSpace
