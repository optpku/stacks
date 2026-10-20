/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.IteratedIntersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.IteratedIntersection

open Scheme.IteratedIntersection

/-- The degree of an ordered nonempty finite family, accumulated from the last
member toward the first. -/
def degree : {n : ℕ} → (Fin (n + 1) → ℤ) → ℤ
  | 0, p => p 0
  | n + 1, p => p (Fin.last (n + 1)) + degree (fun j ↦ p j.castSucc)

/-- The degree of a singleton family is its unique degree. -/
theorem degree_zero (p : Fin 1 → ℤ) : degree p = p 0 := sorry

/-- The degree of a successor family is the last degree plus the degree of the prefix. -/
theorem degree_succ {n : ℕ} (p : Fin (n + 2) → ℤ) :
    degree p = p (Fin.last (n + 1)) + degree (fun j ↦ p j.castSucc) := sorry

/-- The recursively accumulated degree agrees with the finite sum. -/
theorem degree_eq_sum {n : ℕ} (p : Fin (n + 1) → ℤ) :
    degree p = ∑ j, p j := sorry

/-- The ordered product of bivariant classes on a recursively chosen nonempty
intersection, with the last class multiplied on the left. -/
def mul {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Y : Fin (n + 1) → Over S) (f : ∀ j, Y j ⟶ X)
    [hY : ∀ j, LocallyOfFiniteType (Y j).hom]
    [hproper : ∀ j, IsProper (f j).left]
    (p : Fin (n + 1) → ℤ) (c : ∀ j, BivariantClass delta (f j) (p j)) :
    BivariantClass delta (toTarget Y f) (degree p) :=
  match n, Y, f, hY, hproper, p, c with
  | 0, _, _, _, _, _, c => c 0
  | n + 1, Y, f, _, _, p, c =>
      intersectionMul delta
        (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))
        (pullback.fst (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (pullback.snd (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (toTarget Y f) (object_succ_isPullback Y f) rfl
        (c (Fin.last (n + 1)))
        (mul delta (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
          (fun j ↦ p j.castSucc) (fun j ↦ c j.castSucc))

/-- The ordered product of a singleton family is its unique class. -/
theorem mul_zero {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom]
    (Y : Fin 1 → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, LocallyOfFiniteType (Y j).hom]
    [∀ j, IsProper (f j).left]
    (p : Fin 1 → ℤ) (c : ∀ j, BivariantClass delta (f j) (p j)) :
    mul delta Y f p c = c 0 := sorry

/-- The ordered product of a successor family multiplies the last class on the left
of the product of the prefix. -/
theorem mul_succ {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Y : Fin (n + 2) → Over S) (f : ∀ j, Y j ⟶ X)
    [∀ j, LocallyOfFiniteType (Y j).hom]
    [∀ j, IsProper (f j).left]
    (p : Fin (n + 2) → ℤ) (c : ∀ j, BivariantClass delta (f j) (p j)) :
    mul delta Y f p c =
      intersectionMul delta
        (f (Fin.last (n + 1)))
        (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc))
        (pullback.fst (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (pullback.snd (f (Fin.last (n + 1)))
          (toTarget (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)))
        (toTarget Y f) (object_succ_isPullback Y f) rfl
        (c (Fin.last (n + 1)))
        (mul delta (fun j ↦ Y j.castSucc) (fun j ↦ f j.castSucc)
          (fun j ↦ p j.castSucc) (fun j ↦ c j.castSucc)) := sorry

end AlgebraicGeometry.BivariantClass.IteratedIntersection
