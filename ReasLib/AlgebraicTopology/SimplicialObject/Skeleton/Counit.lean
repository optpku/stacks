module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Low-degree behavior of the simplicial skeleton counit

The counit of the skeleton/truncation adjunction is an isomorphism in every degree retained by
the truncation. This is the category-generic input for later subobject and homological
identifications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A]

/-- The skeleton counit is an isomorphism in every simplicial degree at most its truncation
bound. -/
@[stacks 018P "low-degree skeleton counit isomorphism"]
theorem counit.app_isIso_of_le (n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A n]
    (U : SimplicialObject A) {i : ℕ} (hi : i ≤ n) :
    IsIso (((skAdj n).counit.app U).app (op ⦋i⦌)) := sorry

end CategoryTheory.SimplicialObject.Skeleton
