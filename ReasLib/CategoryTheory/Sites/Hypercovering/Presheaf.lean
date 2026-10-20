module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Augmentation
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of simplicial presheaves associated to hypercoverings

This leaf records the sheafified homology consequences of the simplicial presheaf and
augmentation owned by `Hypercovering.Presheaf.Augmentation`.
-/

@[expose] public section

noncomputable section

universe w u v

namespace CategoryTheory

open Limits
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}
variable [HasPullbacks C]

namespace Hypercovering.Homology

/-- Lemma 25.4.5 (1): the simplicial presheaf associated to a hypercovering has vanishing
positive-degree homology sheaves. -/
@[stacks 01GF]
theorem succ_isZero
    [HasSheafify J AddCommGrpCat.{max w v}]
    (K : Hypercovering.{w} J X) (n : ℕ) :
    IsZero ((SimplicialPresheaf.Homology.functor J (n + 1)).obj K.simplicialPresheaf) := sorry

/-- Lemma 25.4.5 (2): the degree-zero homology comparison induced by the hypercovering
augmentation is an isomorphism. -/
@[stacks 01GF]
theorem augmentationMap_isIso
    [HasSheafify J AddCommGrpCat.{max w v}]
    (K : Hypercovering.{w} J X) :
    IsIso (SimplicialPresheaf.Homology.augmentationMap J
      (hypercoveringAugmentedPresheaf K.simplicialFamily K.augmentation)) := sorry

end Hypercovering.Homology

end CategoryTheory
