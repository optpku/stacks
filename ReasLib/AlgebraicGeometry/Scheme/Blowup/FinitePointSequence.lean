/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite composable sequence of blowups at closed points, indexed by its initial and
terminal schemes. -/
inductive PointBlowupSequence : Scheme.{u} → Scheme.{u} → Type (u + 1) where
  /-- The empty sequence from a scheme to itself. -/
  | nil (X : Scheme.{u}) : PointBlowupSequence X X
  /-- Prepend the blowup of a closed point to a finite sequence. -/
  | cons {X X' Y : Scheme.{u}} (p : closedPoints X) (f : X' ⟶ X)
      (h_blowup : IsBlowup f
        (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
      (tail : PointBlowupSequence X' Y) : PointBlowupSequence X Y

namespace PointBlowupSequence

/-- The number of blowups in a finite closed-point blowup sequence. -/
def length {X Y : Scheme.{u}} : PointBlowupSequence X Y → ℕ
  | .nil _ => 0
  | .cons _ _ _ tail => tail.length + 1

/-- The empty closed-point blowup sequence has length zero. -/
theorem length_nil (X : Scheme.{u}) : (nil X).length = 0 := sorry

/-- Prepending one closed-point blowup increases the sequence length by one. -/
theorem length_cons {X X' Y : Scheme.{u}} (p : closedPoints X) (f : X' ⟶ X)
    (h_blowup : IsBlowup f
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : PointBlowupSequence X' Y) :
    (cons p f h_blowup tail).length = tail.length + 1 := sorry

/-- The composite morphism from the terminal scheme of a closed-point blowup sequence to its
initial scheme. -/
def toSource {X Y : Scheme.{u}} : PointBlowupSequence X Y → (Y ⟶ X)
  | .nil _ => 𝟙 _
  | .cons _ f _ tail => tail.toSource ≫ f

/-- The composite of an empty closed-point blowup sequence is the identity. -/
theorem toSource_nil (X : Scheme.{u}) : (nil X).toSource = 𝟙 X := sorry

/-- The composite of a nonempty closed-point blowup sequence is the tail composite followed by
its first blowup. -/
theorem toSource_cons {X X' Y : Scheme.{u}} (p : closedPoints X) (f : X' ⟶ X)
    (h_blowup : IsBlowup f
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : PointBlowupSequence X' Y) :
    (cons p f h_blowup tail).toSource = tail.toSource ≫ f := sorry

/-- Concatenate two finite closed-point blowup sequences. -/
def append {X Y Z : Scheme.{u}} :
    PointBlowupSequence X Y → PointBlowupSequence Y Z → PointBlowupSequence X Z
  | .nil _, tail => tail
  | .cons p f h_blowup head, tail => .cons p f h_blowup (head.append tail)

/-- The length of a concatenation is the sum of the lengths. -/
theorem length_append {X Y Z : Scheme.{u}} (head : PointBlowupSequence X Y)
    (tail : PointBlowupSequence Y Z) :
    (head.append tail).length = head.length + tail.length := sorry

/-- The composite of a concatenation is the composite of the second sequence followed by the
composite of the first. -/
theorem toSource_append {X Y Z : Scheme.{u}} (head : PointBlowupSequence X Y)
    (tail : PointBlowupSequence Y Z) :
    (head.append tail).toSource = tail.toSource ≫ head.toSource := sorry

end PointBlowupSequence

end AlgebraicGeometry.Scheme
