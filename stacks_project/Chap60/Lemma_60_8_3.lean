/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u

variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)

/-- Lemma 60.8.3: in a fibre square of divided-power thickenings, if the
right-hand thickening map is flat and the upper-right source is the pullback
of the lower-right source along that map, then the upper-left thickening is
the pullback of the two lower thickenings as a scheme. -/
@[stacks 07IA]
theorem crystalline_thickening_pullback
    {c₁ c₂ c₃ c : CRIS S I γ h_compatible X x₀}
    (top : c₃ ⟶ c₂) (left : c₃ ⟶ c₁)
    (bottom : c₁ ⟶ c) (right : c₂ ⟶ c)
    (h_square : IsPullback left top bottom right)
    [Flat right.thickening]
    (h_source : c₂.source.left =
      (pullback right.thickening c.inclusion : Scheme.{u})) :
    c₃.thickening =
      (pullback bottom.thickening right.thickening : Scheme.{u}) := sorry
