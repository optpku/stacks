/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Front and back inclusions of simplices

The two order-preserving inclusions used by the Alexander--Whitney map are useful independently of
that construction.  They are kept in the simplex-category namespace so later simplicial arguments
can state the face maps without rebuilding finite-order embeddings.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory

/-- The front inclusion `⦋p⦌ ⟶ ⦋p + q⦌`, sending `i` to `i`. -/
@[stacks 08QD "front simplex inclusion"]
def front (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ :=
  mkHom (Fin.castLEOrderEmb (Nat.succ_le_succ (Nat.le_add_right p q))).toOrderHom

/-- The back inclusion `⦋q⦌ ⟶ ⦋p + q⦌`, sending `i` to `p + i`. -/
@[stacks 08QD "back simplex inclusion"]
def back (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ :=
  mkHom (Fin.natAddOrderEmb p).toOrderHom

/-- The front inclusion with its target rewritten along an equality `p + q = n`. -/
@[stacks 08QD "front simplex inclusion with target equality"]
def frontOfAddEq (p q n : ℕ) (h : p + q = n) : ⦋p⦌ ⟶ ⦋n⦌ :=
  front p q ≫ eqToHom (congrArg SimplexCategory.mk h)

/-- The back inclusion with its target rewritten along an equality `p + q = n`. -/
@[stacks 08QD "back simplex inclusion with target equality"]
def backOfAddEq (p q n : ℕ) (h : p + q = n) : ⦋q⦌ ⟶ ⦋n⦌ :=
  back p q ≫ eqToHom (congrArg SimplexCategory.mk h)

end SimplexCategory
