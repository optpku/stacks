/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointBlowupSequence

/-- The iterated strict-transform scheme of a morphism along a finite sequence of blowups at
closed points. -/
noncomputable def strictTransform {X Xn Z : Scheme.{u}}
    (s : PointBlowupSequence X Xn) (f : Z ⟶ X) : Scheme.{u} :=
  match s with
  | .nil _ => Z
  | .cons p b _ tail =>
      tail.strictTransform
        (AlgebraicGeometry.strictTransformSnd b
          ((IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)).comap b) f)

/-- The canonical morphism from an iterated strict transform to the terminal scheme of the
blowup sequence. -/
noncomputable def strictTransformToTarget {X Xn Z : Scheme.{u}}
    (s : PointBlowupSequence X Xn) (f : Z ⟶ X) : s.strictTransform f ⟶ Xn :=
  match s with
  | .nil _ => f
  | .cons p b _ tail =>
      tail.strictTransformToTarget
        (AlgebraicGeometry.strictTransformSnd b
          ((IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)).comap b) f)

/-- An empty blowup sequence leaves the source scheme unchanged under strict transform. -/
theorem strictTransform_nil {X Z : Scheme.{u}} (f : Z ⟶ X) :
    (PointBlowupSequence.nil X).strictTransform f = Z := sorry

/-- Strict transform along a nonempty sequence first takes the one-step strict transform and
then continues along the tail. -/
theorem strictTransform_cons {X X' Xn Z : Scheme.{u}} (p : closedPoints X) (b : X' ⟶ X)
    (h_blowup : IsBlowup b
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : PointBlowupSequence X' Xn) (f : Z ⟶ X) :
    (PointBlowupSequence.cons p b h_blowup tail).strictTransform f =
      tail.strictTransform
        (AlgebraicGeometry.strictTransformSnd b
          ((IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)).comap b) f) := sorry

/-- For an empty blowup sequence, the canonical map to the terminal scheme is the original
morphism. -/
theorem strictTransformToTarget_nil {X Z : Scheme.{u}} (f : Z ⟶ X) :
    (PointBlowupSequence.nil X).strictTransformToTarget f = f := sorry

/-- For a nonempty blowup sequence, the canonical terminal map is obtained by applying the
tail construction to the one-step strict-transform projection. -/
theorem strictTransformToTarget_cons {X X' Xn Z : Scheme.{u}}
    (p : closedPoints X) (b : X' ⟶ X)
    (h_blowup : IsBlowup b
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : PointBlowupSequence X' Xn) (f : Z ⟶ X) :
    (PointBlowupSequence.cons p b h_blowup tail).strictTransformToTarget f =
      tail.strictTransformToTarget
        (AlgebraicGeometry.strictTransformSnd b
          ((IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)).comap b) f) := sorry

/-- Iterated strict transform preserves a closed immersion into the ambient scheme. -/
instance instIsClosedImmersionToTarget {X Xn Z : Scheme.{u}}
    (s : PointBlowupSequence X Xn) (f : Z ⟶ X) [IsClosedImmersion f] :
    IsClosedImmersion (s.strictTransformToTarget f) := sorry

end AlgebraicGeometry.Scheme.PointBlowupSequence
