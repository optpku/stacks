/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The open complement of the image of an integral morphism of schemes. -/
def integralImageComplement {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] : Y.Opens :=
  ⟨(Set.range f.base)ᶜ, isOpen_compl_iff.2 (Scheme.Hom.isClosedMap f).isClosed_range⟩

/-- The carrier of the integral image complement is the complement of the image. -/
theorem integralImageComplement_carrier {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] :
    (integralImageComplement f : Set Y) = (Set.range f.base)ᶜ := sorry

end AlgebraicGeometry
