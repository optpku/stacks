/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smooth morphisms of commutative rings

This leaf connects ring-theoretic smoothness with finite presentability in the
category of commutative rings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommRingCat

/-- A smooth morphism of commutative rings is finitely presentable as a
morphism in `CommRingCat`. -/
theorem isFinitelyPresentable_hom_of_smooth
    {X Y : CommRingCat.{u}} (f : X ⟶ Y)
    (hf : (RingHom.toMorphismProperty RingHom.Smooth) f) :
    CategoryTheory.MorphismProperty.isFinitelyPresentable CommRingCat f := sorry

end CommRingCat
