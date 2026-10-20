module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Recursive

/-!
# Computations for Recursive Finite Postnikov Systems

This leaf exposes the stable projections of the zero and successor
constructors. It keeps downstream code independent of the internal `Step`
representation of recursive Postnikov data.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The head of a zero-length system is the object supplied to `mk₀`. -/
@[simp, stacks 0D7Z]
theorem mk₀_head {X : ComposableArrows D 0} (Y : D) (toX : Y ⟶ X.obj 0) [IsIso toX] :
    (mk₀ Y toX).head = Y := sorry

/-- The head comparison of a zero-length system is the map supplied to `mk₀`. -/
@[simp, stacks 0D7Z]
theorem mk₀_headToX {X : ComposableArrows D 0} (Y : D) (toX : Y ⟶ X.obj 0) [IsIso toX] :
    (mk₀ Y toX).headToX = toX := sorry

/-- The head of a successor system is the new object supplied to `mkSucc`. -/
@[simp, stacks 0D7Z]
theorem mkSucc_head {n : ℕ} {X : ComposableArrows D (n + 1)}
    (tail : PostnikovSystem X.δ₀) (Y : D) (toX : Y ⟶ X.obj 0)
    (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    (mkSucc tail Y toX toNext connecting distinguished comp).head = Y := sorry

/-- The head comparison of a successor system is the new comparison supplied to `mkSucc`. -/
@[simp, stacks 0D7Z]
theorem mkSucc_headToX {n : ℕ} {X : ComposableArrows D (n + 1)}
    (tail : PostnikovSystem X.δ₀) (Y : D) (toX : Y ⟶ X.obj 0)
    (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    (mkSucc tail Y toX toNext connecting distinguished comp).headToX = toX := sorry

/-- Removing the new step of a successor system recovers its supplied tail. -/
@[simp, stacks 0D7Z]
theorem mkSucc_tail {n : ℕ} {X : ComposableArrows D (n + 1)}
    (tail : PostnikovSystem X.δ₀) (Y : D) (toX : Y ⟶ X.obj 0)
    (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    (mkSucc tail Y toX toNext connecting distinguished comp).tail = tail := sorry

/-- The second map of a successor system is the map supplied to `mkSucc`. -/
@[simp, stacks 0D7Z]
theorem mkSucc_headToNext {n : ℕ} {X : ComposableArrows D (n + 1)}
    (tail : PostnikovSystem X.δ₀) (Y : D) (toX : Y ⟶ X.obj 0)
    (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    (mkSucc tail Y toX toNext connecting distinguished comp).headToNext = toNext := sorry

/-- The connecting map of a successor system is the map supplied to `mkSucc`. -/
@[simp, stacks 0D7Z]
theorem mkSucc_headConnecting {n : ℕ} {X : ComposableArrows D (n + 1)}
    (tail : PostnikovSystem X.δ₀) (Y : D) (toX : Y ⟶ X.obj 0)
    (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    (mkSucc tail Y toX toNext connecting distinguished comp).headConnecting = connecting := sorry

end CategoryTheory.PostnikovSystem
