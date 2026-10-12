/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Recursive
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Construction of Finite Postnikov Systems

This leaf owns the reusable successor construction: a Postnikov system on the
tail and a factorization of the first differential determine a Postnikov
system on the whole row.
-/

open CategoryTheory.ComposableArrows

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

namespace PostnikovSystem

/-- A factorization of the first differential through the head of a tail Postnikov system
extends that tail system to the whole row. -/
@[stacks 0D81]
theorem nonempty_of_tail_factor {n : ℕ} {X : ComposableArrows D (n + 1)}
    (P : PostnikovSystem X.δ₀) (f : X.obj 0 ⟶ P.head)
    (hf : f ≫ P.headToX = X.map' 0 1) :
    Nonempty (PostnikovSystem X) := sorry

end PostnikovSystem

end

end CategoryTheory
