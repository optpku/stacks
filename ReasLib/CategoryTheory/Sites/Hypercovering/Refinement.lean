module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise refinements of hypercoverings

This leaf records the refinement-existence interface used to prescribe a
covering map in one simplicial degree of a fixed-target hypercovering.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open SemiRepresentableFamily.OverFamily
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]

namespace Hypercovering.Refinement

/-- A covering map into one degree of a hypercovering can be realized as a factor of a degreewise
map from a refining hypercovering. -/
@[stacks 01GJ "refinement factoring a prescribed degree map"]
theorem existsDegreeFactorization
    {X : C} (K : Hypercovering J X) (n : ℕ) (Z : SR(C, X))
    (u : Z ⟶ K.toSimplicialObject.obj (op <| SimplexCategory.mk n))
    (hu : SemiRepresentableFamily.OverFamily.covering J u) :
    ∃ (L : Hypercovering J X)
      (f : L ⟶ K)
      (g : L.toSimplicialObject.obj (op <| SimplexCategory.mk n) ⟶ Z),
      (Hom.toSimplicial f).app (op <| SimplexCategory.mk n) = g ≫ u := sorry

end Hypercovering.Refinement

end CategoryTheory
