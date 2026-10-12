/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.Skeleton
import StacksCheckRecall

/-!
@stack 017T
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

variable (U : SSet.{u}) (n m : ℕ)

/- Lemma 14.18.4 (017T) (1): the textbook union of images is the degreewise membership API of
the canonical subcomplex `U.skeleton (n + 1)`. -/
@[stacks 017T "degreewise description"]
#check (SSet.skeleton.succ.obj_eq_generated U n m :
  (U.skeleton (n + 1)).obj (op ⦋m⦌) =
    { x : U _⦋m⦌ | ∃ i ≤ n, ∃ φ : ⦋m⦌ ⟶ ⦋i⦌, x ∈ Set.range (U.map φ.op) })

variable (d : ℕ) (hd : d ≤ n)

/- Lemma 14.18.4 (017T) (2): in every degree `d ≤ n`, the generated subcomplex is the
whole degree of `U`. -/
@[stacks 017T "agreement in retained degrees"]
#check (SSet.skeleton_obj_eq_top U (Nat.lt_succ_of_le hd) :
  (U.skeleton (n + 1)).obj (op ⦋d⦌) = ⊤)

/- Lemma 14.18.4 (017T) (3): the generated subcomplex has the canonical dimension bound. -/
@[stacks 017T "dimension bound"]
#check (inferInstance : ((U.skeleton (n + 1) : SSet)).HasDimensionLT (n + 1))

variable (h : n < m) (x : (U.skeleton (n + 1) : SSet) _⦋m⦌)

/- Lemma 14.18.4 (017T) (4): all simplices above degree `n` are degenerate. -/
@[stacks 017T "high-degree degeneracy"]
#check (SSet.skeleton.succ.mem_degenerate_of_lt U h x :
  x ∈ (U.skeleton (n + 1) : SSet).degenerate m)

end SSet
