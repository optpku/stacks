/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.CategoryTheory.Limits.Colimit.Representable.Factorization
public import ReasLib.CategoryTheory.Limits.Types.Filtered.Representatives

@[expose] public section

/-!
# Rank-Collapse Systems and Representable Colimits

Given `rank : α → ℕ`, this leaf constructs the sequential system obtained by successively
identifying elements of bounded rank. Its colimit is a point, while an unbounded rank function
exhibits failure of injectivity for the corresponding representable-colimit comparison.
-/

open CategoryTheory Opposite

universe u

namespace CategoryTheory.Limits.Types.RankCollapse

variable {α : Type u}

/-- At stage `n`, two elements are related when they are equal or both have rank at most `n`. -/
def rel (rank : α → ℕ) (n : ℕ) (a b : α) : Prop :=
  a = b ∨ rank a ≤ n ∧ rank b ≤ n

/-- The bounded-rank collapse relation is an equivalence relation. -/
theorem rel_equivalence (rank : α → ℕ) (n : ℕ) :
    _root_.Equivalence (rel rank n) := sorry

/-- The setoid that collapses all elements of rank at most `n` to one class. -/
def setoid (rank : α → ℕ) (n : ℕ) : Setoid α where
  r := rel rank n
  iseqv := rel_equivalence rank n

/-- The quotient obtained by collapsing all elements of rank at most `n`. -/
abbrev Stage (rank : α → ℕ) (n : ℕ) : Type u :=
  Quotient (setoid rank n)

/-- The quotient projection to the `n`th bounded-rank collapse. -/
def projection (rank : α → ℕ) (n : ℕ) : α ⟶ Stage rank n :=
  ↾fun a ↦ Quotient.mk (setoid rank n) a

/-- Increasing the rank bound preserves the collapse relation. -/
theorem map_respects (rank : α → ℕ) {n m : ℕ} (h : n ≤ m) :
    ∀ a b, (setoid rank n).r a b → (setoid rank m).r a b := sorry

/-- The transition map between two bounded-rank collapses. -/
def map (rank : α → ℕ) {n m : ℕ} (h : n ≤ m) :
    Stage rank n ⟶ Stage rank m :=
  ↾Quotient.map id (map_respects rank h)

/-- A transition map sends the class of an element to the class of the same element. -/
theorem map_projection (rank : α → ℕ) {n m : ℕ} (h : n ≤ m) (a : α) :
    map rank h (projection rank n a) = projection rank m a := sorry

/-- The sequential diagram of bounded-rank collapses. -/
@[stacks 05NQ "rank-collapse diagram"]
def diagram (rank : α → ℕ) : ℕ ⥤ Type u :=
  Functor.ofSequence fun n ↦ map rank (Nat.le_succ n)

/-- Every structure map sends an element to the class of that element at the later stage. -/
theorem diagram_map_projection (rank : α → ℕ) {n m : ℕ} (h : n ≤ m) (a : α) :
    (diagram rank).map (homOfLE h) (projection rank n a) =
      projection rank m a := sorry

/-- The colimit of the bounded-rank collapse diagram is subsingleton. -/
instance colimitSubsingleton (rank : α → ℕ) :
    Subsingleton (colimit (diagram rank)) := sorry

/-- The unique map from the collapse colimit to the one-point type. -/
noncomputable def toPUnit (rank : α → ℕ) :
    colimit (diagram rank) ⟶ PUnit :=
  ↾fun _ ↦ PUnit.unit

/-- A chosen element supplies the inverse map from the one-point type to the colimit. -/
noncomputable def fromPUnit (rank : α → ℕ) (base : α) :
    PUnit ⟶ colimit (diagram rank) :=
  ↾fun _ ↦ colimit.ι (diagram rank) 0 (projection rank 0 base)

/-- The chosen point is the unique preimage of every colimit element. -/
theorem fromPUnit_toPUnit (rank : α → ℕ) (base : α) (x : colimit (diagram rank)) :
    fromPUnit rank base (toPUnit rank x) = x := sorry

/-- The map to the one-point type is inverse to the chosen map from it. -/
theorem toPUnit_fromPUnit (rank : α → ℕ) (base : α) (x : PUnit) :
    toPUnit rank (fromPUnit rank base x) = x := sorry

/-- Example 19.2.2 (05NQ): for a chosen element, the collapse colimit is explicitly equivalent
to a one-point type. -/
@[stacks 05NQ "one-point colimit"]
noncomputable def colimitEquivPUnit (rank : α → ℕ) (base : α) :
    colimit (diagram rank) ≃ PUnit where
  toFun := toPUnit rank
  invFun := fromPUnit rank base
  left_inv := fromPUnit_toPUnit rank base
  right_inv := toPUnit_fromPUnit rank base

/-- The constant map from `α` to the class of `base` at stage `n`. -/
def baseConstant (rank : α → ℕ) (base : α) (n : ℕ) :
    α ⟶ Stage rank n :=
  ↾fun _ ↦ projection rank n base

/-- The quotient projections form a coherent family in the represented-Hom diagram. -/
theorem projection_naturality (rank : α → ℕ) {n m : ℕ} (h : n ≤ m) :
    (diagram rank ⋙ coyoneda.obj (op α)).map (homOfLE h) (projection rank n) =
      projection rank m := sorry

/-- The constant maps form a coherent family in the represented-Hom diagram. -/
theorem baseConstant_naturality (rank : α → ℕ) (base : α) {n m : ℕ} (h : n ≤ m) :
    (diagram rank ⋙ coyoneda.obj (op α)).map (homOfLE h) (baseConstant rank base n) =
      baseConstant rank base m := sorry

/-- When the rank is unbounded, the quotient projection at any stage is not constant. -/
theorem projection_ne_baseConstant (rank : α → ℕ) (base : α)
    (h_unbounded : ∀ n, ∃ a : α, n < rank a) (n : ℕ) :
    projection rank n ≠ baseConstant rank base n := sorry

/-- For an unbounded rank, the projection and constant families determine distinct elements of
the represented-Hom colimit. -/
theorem projectionClass_ne_constantClass (rank : α → ℕ) (base : α)
    (h_unbounded : ∀ n, ∃ a : α, n < rank a) (n : ℕ) :
    colimit.ι (diagram rank ⋙ coyoneda.obj (op α)) n (projection rank n) ≠
      colimit.ι (diagram rank ⋙ coyoneda.obj (op α)) n
        (baseConstant rank base n) := sorry

/-- The representable-colimit comparison identifies the projection and constant classes. -/
theorem comparison_projection_eq_baseConstant (rank : α → ℕ) (base : α) (n : ℕ) :
    colimit.post (diagram rank) (coyoneda.obj (op α))
        (colimit.ι (diagram rank ⋙ coyoneda.obj (op α)) n (projection rank n)) =
      colimit.post (diagram rank) (coyoneda.obj (op α))
        (colimit.ι (diagram rank ⋙ coyoneda.obj (op α)) n
          (baseConstant rank base n)) := sorry

/-- An unbounded rank function produces a noninjective representable-colimit comparison. -/
theorem comparison_not_injective (rank : α → ℕ) (base : α)
    (h_unbounded : ∀ n, ∃ a : α, n < rank a) :
    ¬ Function.Injective (colimit.post (diagram rank) (coyoneda.obj (op α))) := sorry

namespace Nat

/-- Example 19.2.2 (05NQ): the natural-number projection and zero-constant maps remain distinct
in the represented-Hom colimit. -/
@[stacks 05NQ "distinct projection and constant classes"]
theorem projectionClass_ne_zeroConstant (n : ℕ) :
    colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
        (projection (id : ℕ → ℕ) n) ≠
      colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
        (baseConstant (id : ℕ → ℕ) 0 n) := sorry

/-- Example 19.2.2 (05NQ): those two classes have the same image under the representable-colimit
comparison. -/
@[stacks 05NQ "equal projection and constant images"]
theorem comparison_projection_eq_zeroConstant (n : ℕ) :
    colimit.post (diagram (id : ℕ → ℕ)) (coyoneda.obj (op ℕ))
        (colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
          (projection (id : ℕ → ℕ) n)) =
      colimit.post (diagram (id : ℕ → ℕ)) (coyoneda.obj (op ℕ))
        (colimit.ι (diagram (id : ℕ → ℕ) ⋙ coyoneda.obj (op ℕ)) n
          (baseConstant (id : ℕ → ℕ) 0 n)) := sorry

/-- Example 19.2.2 (05NQ): the representable-colimit comparison for the natural-number collapse
system is not injective. -/
@[stacks 05NQ "representable comparison not injective"]
theorem comparison_not_injective :
    ¬ Function.Injective
      (colimit.post (diagram (id : ℕ → ℕ)) (coyoneda.obj (op ℕ))) := sorry

end Nat

end CategoryTheory.Limits.Types.RankCollapse
