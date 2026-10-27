/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A functor on schemes over `B` is smooth over `B` if it is represented by
a smooth morphism of algebraic spaces to `B`. -/
def IsSmoothOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (Y : AlgebraicSpace S) (π : Y ⟶ B), Smooth π ∧ Nonempty (F ≅ yonedaOver π)

/-- Smoothness over `B` is existence of a smooth representing morphism and an
isomorphism to its relative functor of points. -/
theorem isSmoothOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsSmoothOver F ↔
      ∃ (Y : AlgebraicSpace S) (π : Y ⟶ B),
        Smooth π ∧ Nonempty (F ≅ yonedaOver π) := sorry

/-- For a represented functor, smoothness over the base is equivalent to
smoothness of its representing morphism. -/
theorem isSmoothOver_iff_of_representable {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    {Y : AlgebraicSpace S} {π : Y ⟶ B} (e : F ≅ yonedaOver π) :
    IsSmoothOver F ↔ Smooth π := sorry

end AlgebraicGeometry.AlgebraicSpace
