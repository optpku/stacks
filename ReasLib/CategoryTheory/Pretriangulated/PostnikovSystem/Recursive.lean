/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Recursive Finite Postnikov Systems

This leaf owns the recursive data of a Postnikov system on a finite row of
composable arrows in a pretriangulated category. It deliberately stops at the
head step; `Stages` owns the indexed view and its computation API.
-/

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

namespace PostnikovSystem

/-- The recursive step data of a finite Postnikov system. At length zero it records an
isomorphism to the sole row object. At a successor length it records the tail system, a new
distinguished triangle, and the factorization of the first row differential. -/
@[stacks 0D7Z]
inductive Step : {n : ℕ} → (X : ComposableArrows D n) → (Y : D) → (toX : Y ⟶ X.obj 0) →
    Type (max u v)
  /-- The zero-length step is an isomorphism to the sole row object. -/
  | zero {X : ComposableArrows D 0} {Y : D} (toX : Y ⟶ X.obj 0) [IsIso toX] :
      Step X Y toX
  /-- A successor step adjoins one distinguished triangle to a step on the truncated row. -/
  | succ {n : ℕ} {X : ComposableArrows D (n + 1)} {Y : D} {toX : Y ⟶ X.obj 0}
      {Y' : D} {toX' : Y' ⟶ X.δ₀.obj 0} (tail : Step X.δ₀ Y' toX')
      (toNext : X.obj 0 ⟶ Y') (connecting : Y' ⟶ Y⟦(1 : ℤ)⟧)
      (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
      (comp : toNext ≫ toX' = X.map' 0 1) :
      Step X Y toX

end PostnikovSystem

/-- A Postnikov system on a finite row of composable arrows in a pretriangulated category. Its
recursive `step` records the auxiliary objects, stage triangles, and factorizations of the row
differentials. -/
@[stacks 0D7Z "recursive Postnikov system"]
structure PostnikovSystem {n : ℕ} (X : ComposableArrows D n) where
  /-- The auxiliary object at the left end of the recursive construction. -/
  head : D
  /-- The comparison morphism from the left-end auxiliary object to the row. -/
  headToX : head ⟶ X.obj 0
  /-- The recursive step data. -/
  step : PostnikovSystem.Step X head headToX

namespace PostnikovSystem

/-- Construct a zero-length Postnikov system from an isomorphism to the sole row object. -/
@[stacks 0D7Z]
def mk₀ {X : ComposableArrows D 0} (Y : D) (toX : Y ⟶ X.obj 0) [IsIso toX] :
    PostnikovSystem X :=
  ⟨Y, toX, .zero toX⟩

/-- Extend a Postnikov system on the truncated row by one distinguished triangle. -/
@[stacks 0D7Z]
def mkSucc {n : ℕ} {X : ComposableArrows D (n + 1)} (tail : PostnikovSystem X.δ₀) (Y : D)
    (toX : Y ⟶ X.obj 0) (toNext : X.obj 0 ⟶ tail.head) (connecting : tail.head ⟶ Y⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk toX toNext connecting ∈ distTriang D)
    (comp : toNext ≫ tail.headToX = X.map' 0 1) :
    PostnikovSystem X :=
  ⟨Y, toX, .succ tail.step toNext connecting distinguished comp⟩

/-- The Postnikov system obtained by removing the leftmost recursive step. -/
@[stacks 0D7Z]
def tail {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    PostnikovSystem X.δ₀ :=
  match P.step with
  | .succ tail _ _ _ _ => ⟨_, _, tail⟩

/-- The second triangle map from the row into the head of the tail Postnikov system. -/
@[stacks 0D7Z]
def headToNext {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    X.obj 0 ⟶ P.tail.head :=
  match P with
  | ⟨_, _, .succ _ toNext _ _ _⟩ => toNext

/-- The connecting map of the distinguished triangle at the head of a nonzero system. -/
@[stacks 0D7Z]
def headConnecting {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.tail.head ⟶ P.head⟦(1 : ℤ)⟧ :=
  match P with
  | ⟨_, _, .succ _ _ connecting _ _⟩ => connecting

/-- The triangle at the head of a nonzero Postnikov system is distinguished. -/
@[stacks 0D7Z]
theorem head_distinguished {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    Triangle.mk P.headToX P.headToNext P.headConnecting ∈ distTriang D :=
  match P with
  | ⟨_, _, .succ _ _ _ distinguished _⟩ => distinguished

/-- The maps at the head factor the first differential of the finite row. -/
@[stacks 0D7Z]
theorem head_comp {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.headToNext ≫ P.tail.headToX = X.map' 0 1 :=
  match P with
  | ⟨_, _, .succ _ _ _ _ comp⟩ => comp

end PostnikovSystem

end

end CategoryTheory
