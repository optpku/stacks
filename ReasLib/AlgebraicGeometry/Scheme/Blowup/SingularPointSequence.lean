/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite sequence of blowups whose center at every stage is a singular closed point. -/
inductive SingularPointBlowupSequence : Scheme.{u} → Scheme.{u} → Type (u + 1) where
  /-- The empty sequence from a scheme to itself. -/
  | nil (X : Scheme.{u}) : SingularPointBlowupSequence X X
  /-- Prepend the blowup of a singular closed point to a finite sequence. -/
  | cons {X X' Y : Scheme.{u}} (p : closedPoints X) (h_singular : p.1 ∈ Sing(X))
      (f : X' ⟶ X)
      (h_blowup : IsBlowup f
        (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
      (tail : SingularPointBlowupSequence X' Y) : SingularPointBlowupSequence X Y

namespace SingularPointBlowupSequence

/-- The number of blowups in a finite singular-point blowup sequence. -/
def length {X Y : Scheme.{u}} : SingularPointBlowupSequence X Y → ℕ
  | .nil _ => 0
  | .cons _ _ _ _ tail => tail.length + 1

/-- The empty singular-point blowup sequence has length zero. -/
theorem length_nil (X : Scheme.{u}) : (nil X).length = 0 := sorry

/-- Prepending one blowup increases the length by one. -/
theorem length_cons {X X' Y : Scheme.{u}} (p : closedPoints X)
    (h_singular : p.1 ∈ Sing(X)) (f : X' ⟶ X)
    (h_blowup : IsBlowup f
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : SingularPointBlowupSequence X' Y) :
    (cons p h_singular f h_blowup tail).length = tail.length + 1 := sorry

/-- `EveryTarget s P` says that `P` holds for every post-initial stage of `s`. -/
def EveryTarget {X Y : Scheme.{u}} (s : SingularPointBlowupSequence X Y)
    (P : Scheme.{u} → Prop) : Prop :=
  match s with
  | .nil _ => True
  | @cons _ X' _ _ _ _ _ tail => P X' ∧ tail.EveryTarget P

/-- The empty sequence has no post-initial stages. -/
theorem everyTarget_nil (X : Scheme.{u}) (P : Scheme.{u} → Prop) :
    (nil X).EveryTarget P ↔ True := sorry

/-- `EveryTarget` for a nonempty sequence consists of the first target and the remaining tail. -/
theorem everyTarget_cons {X X' Y : Scheme.{u}} (p : closedPoints X)
    (h_singular : p.1 ∈ Sing(X)) (f : X' ⟶ X)
    (h_blowup : IsBlowup f
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : SingularPointBlowupSequence X' Y) (P : Scheme.{u} → Prop) :
    (cons p h_singular f h_blowup tail).EveryTarget P ↔
      P X' ∧ tail.EveryTarget P := sorry

/-- The composite morphism from the terminal scheme of a singular-point blowup sequence back
to its source scheme. -/
def toSource {X Y : Scheme.{u}} :
    Scheme.SingularPointBlowupSequence X Y → (Y ⟶ X)
  | Scheme.SingularPointBlowupSequence.nil _ => 𝟙 _
  | Scheme.SingularPointBlowupSequence.cons _ _ f _ tail => toSource tail ≫ f

/-- The composite of the empty singular-point blowup sequence is the identity. -/
theorem toSource_nil (X : Scheme.{u}) :
    toSource (Scheme.SingularPointBlowupSequence.nil X) = 𝟙 X := sorry

/-- The composite of a nonempty sequence is its tail composite followed by its first blowup. -/
theorem toSource_cons {X X' Y : Scheme.{u}} (p : closedPoints X)
    (h_singular : p.1 ∈ Sing(X)) (f : X' ⟶ X)
    (h_blowup : IsBlowup f
      (IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)))
    (tail : Scheme.SingularPointBlowupSequence X' Y) :
    toSource (Scheme.SingularPointBlowupSequence.cons p h_singular f h_blowup tail) =
      toSource tail ≫ f := sorry


end SingularPointBlowupSequence

end AlgebraicGeometry.Scheme
