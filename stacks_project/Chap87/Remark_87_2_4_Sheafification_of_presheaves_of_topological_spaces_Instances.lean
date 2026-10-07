module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Sheafification of topological-space-valued presheaves

The inclusion of `TopCat`-valued sheaves into presheaves is a right adjoint. The source
obtains this from the special adjoint functor theorem, using limits and a solution-set
bound on image-generated subsheaves.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The inclusion of `TopCat`-valued sheaves on a site satisfies the solution set
condition. -/
theorem sheafToPresheaf_solutionSetCondition (J : GrothendieckTopology C) :
    SolutionSetCondition.{max u v} (sheafToPresheaf J TopCat.{max u v}) :=
  sorry

/-- `TopCat`-valued sheaves on a site admit sheafification: the inclusion into
presheaves is a right adjoint. -/
instance hasWeakSheafify_topCat (J : GrothendieckTopology C) :
    HasWeakSheafify J TopCat.{max u v} :=
  sorry

end CategoryTheory
