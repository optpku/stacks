module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.Finite
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Matching diagrams for truncated simplicial objects

The next-degree matching diagram is the structured-arrow diagram for the inclusion of
`n`-truncated simplices. Its cone functor is the representation-independent owner of matching
families and is suitable for both explicit constructions and right-Kan-extension arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.matching

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- The structured-arrow category indexing the next-degree matching diagram of an `n`-truncated
simplicial object. -/
@[stacks 0186 "matching index category"]
abbrev index (n : ℕ) :=
  SimplexCategory.Truncated.matchingIndex n (n + 1)

/-- The structured-arrow diagram whose limit is the next matching object of `U`. -/
@[stacks 0186 "matching diagram"]
abbrev diagram (U : SimplicialObject.Truncated C n) : index n ⥤ C :=
  StructuredArrow.proj (op (SimplexCategory.mk (n + 1)))
    (SimplexCategory.Truncated.inclusion n).op ⋙ U

/-- The matching-index object corresponding to the `i`-th coface
`δ_i : [n] ⟶ [n + 1]`. -/
@[stacks 0186 "face object in the matching index"]
def face (i : Fin (n + 2)) : index n :=
  StructuredArrow.mk (Y := op (⦋n⦌ₙ : SimplexCategory.Truncated n))
    ((SimplexCategory.δ i).op :
      op ⦋n + 1⦌ ⟶
        (SimplexCategory.Truncated.inclusion n).op.obj
          (op (⦋n⦌ₙ : SimplexCategory.Truncated n)))

end CategoryTheory.SimplicialObject.Truncated.matching
