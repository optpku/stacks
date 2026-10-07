module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.LocalHypercover
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of presheaf-target hypercoverings

This leaf specializes the generic homology theorem for local hypercovers to simplicial
semi-representable augmentations.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf

open Limits

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

namespace Homology

/-- The positive-degree homology sheaves of the simplicial presheaf of a hypercovering vanish. -/
@[stacks 01GE "presheaf-target positive degrees"]
theorem succ_isZero (H : HypercoveringOf J 𝒢) (n : ℕ) :
    IsZero ((SimplicialPresheaf.Homology.functor J (n + 1)).obj
      (hypercoveringPresheaf H.simplicial)) := sorry

/-- The degree-`0` homology of a hypercovering identifies with the free abelian sheaf on its
target. -/
@[stacks 01GE "presheaf-target degree zero"]
theorem augmentationMap_isIso (H : HypercoveringOf J 𝒢) :
    IsIso (SimplicialPresheaf.Homology.augmentationMap J
      (hypercoveringAugmentedPresheaf H.simplicial H.augmentation)) := sorry

end Homology

end CategoryTheory.HypercoveringOf
