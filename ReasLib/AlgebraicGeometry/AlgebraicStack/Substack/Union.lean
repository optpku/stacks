/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack

/-!
# Unions of open substacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicStack.Substack

/-- Any family of open substacks has an open union containing each member as an
open substack. An object belongs to the union exactly when arrows from objects
in the members jointly cover its base scheme on points. -/
theorem exists_iUnion {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {I : Type v} (P : I → ObjectProperty X.total) (hP : ∀ i, IsOpen X (P i)) :
    ∃ Q : ObjectProperty X.total, IsOpen X Q ∧ (∀ i, P i ≤ Q) ∧
      (∀ (hQ : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p)) (i : I),
        IsOpen (category X Q hQ) (fun z ↦ P i z.obj)) ∧
      (∀ x : X.total, Q x ↔ ∀ t : (X.p.obj x).left,
        ∃ (i : I) (y : X.total) (f : y ⟶ x) (s : (X.p.obj y).left),
          P i y ∧ (X.p.map f).left.base s = t) := sorry

/-- An object belongs to the union of a family of substacks when arrows from
objects in the family jointly cover every point of its base scheme. -/
def iUnion {S : Scheme.{u}} {X : GroupoidsOver S} {I : Type v}
    (P : I → ObjectProperty X.total) : ObjectProperty X.total :=
  fun x ↦ ∀ t : (X.p.obj x).left,
    ∃ (i : I) (y : X.total) (f : y ⟶ x) (s : (X.p.obj y).left),
      P i y ∧ (X.p.map f).left.base s = t

/-- Membership in the union means that each point of the base scheme is in
the image of an arrow from an object in one of the family members. -/
theorem iUnion_iff {S : Scheme.{u}} {X : GroupoidsOver S} {I : Type v}
    (P : I → ObjectProperty X.total) (x : X.total) :
    iUnion P x ↔ ∀ t : (X.p.obj x).left,
      ∃ (i : I) (y : X.total) (f : y ⟶ x) (s : (X.p.obj y).left),
        P i y ∧ (X.p.map f).left.base s = t := Iff.rfl

/-- The union of a family of open substacks is an open substack. -/
theorem isOpen_iUnion {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {I : Type v} (P : I → ObjectProperty X.total) (hP : ∀ i, IsOpen X (P i)) :
    IsOpen X (iUnion P) := by
  obtain ⟨Q, hQ, _, _, hmem⟩ := exists_iUnion P hP
  have h : Q = iUnion P := funext fun x ↦ propext (hmem x)
  exact h ▸ hQ

end AlgebraicGeometry.AlgebraicStack.Substack
