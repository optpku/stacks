module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Closed

/-!
# Closed immersions of topoi

This leaf owns the closed-immersion condition on a morphism of topoi.  Its
exactness consequences live in the downstream `ClosedImmersion/Exactness` leaf.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A closed immersion is an embedding whose direct image has closed-subtopos essential image. -/
@[stacks 08M0, mk_iff isClosedImmersion_iff_embedding_and_closedSubtopos]
class IsClosedImmersion (f : MorphismOfTopoiIn J K) : Prop extends IsEmbedding f where
  /-- The essential image of direct image is a closed subtopos. -/
  isClosedSubtopos : GrothendieckTopology.IsClosedSubtopos f.pushforward.essImage

end CategoryTheory.MorphismOfTopoiIn
