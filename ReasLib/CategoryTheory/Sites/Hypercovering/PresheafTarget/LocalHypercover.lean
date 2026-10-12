/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented.LocalHypercover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local hypercovers of presheaves

This leaf specializes the generic local-hypercover predicate to augmentations by simplicial
semi-representable families. Terminal-target specializations, sheafification consequences, and
homology consequences live in separate leaves.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits Opposite
open scoped CategoryTheory.SemiRepresentableFamily Simplicial

variable {C : Type u} [Category.{v} C]

/-- The simplicial presheaf represented by a simplicial semi-representable family. -/
noncomputable abbrev hypercoveringPresheaf (K : SimplicialObject (SR(C))) :
    SimplicialObject (Cᵒᵖ ⥤ Type (max w v)) :=
  K ⋙ Limits.FormalCoproduct.toPresheaf

/-- The augmented simplicial presheaf determined by a simplicial semi-representable family and
an augmentation to `𝒢`. -/
@[stacks 09VU "augmented presheaf of a semi-representable family"]
def hypercoveringAugmentedPresheaf
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (K : SimplicialObject (SR(C)))
    (augmentation : hypercoveringPresheaf K ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max w v)) where
  left := hypercoveringPresheaf K
  right := 𝒢
  hom := augmentation

section Target

variable (J : GrothendieckTopology C)

/-- The degree-`0` local-surjectivity condition for an augmentation by a simplicial
semi-representable family. -/
abbrev HypercoveringOf.ZeroLocallySurjective
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (simplicial : SimplicialObject (SR(C)))
    (augmentation : hypercoveringPresheaf simplicial ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) : Prop :=
  Presheaf.IsLocallySurjective J
    (hypercoveringAugmentedPresheaf simplicial augmentation).zeroMap

/-- The degree-`1` local-surjectivity condition for an augmentation by a simplicial
semi-representable family. -/
abbrev HypercoveringOf.OneLocallySurjective
    {𝒢 : Cᵒᵖ ⥤ Type (max w v)}
    (simplicial : SimplicialObject (SR(C)))
    (augmentation : hypercoveringPresheaf simplicial ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) : Prop :=
  Presheaf.IsLocallySurjective J
    (hypercoveringAugmentedPresheaf simplicial augmentation).oneMap

/-- The higher matching-map local-surjectivity condition for a simplicial
semi-representable family. -/
abbrev HypercoveringOf.HigherLocallySurjective
    (simplicial : SimplicialObject (SR(C))) (n : ℕ) : Prop :=
  Presheaf.IsLocallySurjective J
    (SimplicialObject.matchingMap (hypercoveringPresheaf simplicial) n)

/-- Definition 25.6.1 (1): a hypercovering of a presheaf `𝒢` is a simplicial
semi-representable family whose induced augmentation is a local hypercover. -/
@[stacks 09VU "hypercovering of a presheaf"]
structure HypercoveringOf (𝒢 : Cᵒᵖ ⥤ Type (max w v)) where
  /-- The underlying simplicial semi-representable family. -/
  simplicial : SimplicialObject (SR(C))
  /-- The augmentation to the target presheaf. -/
  augmentation : hypercoveringPresheaf simplicial ⟶
    (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢
  /-- The induced augmented simplicial presheaf is a local hypercover. -/
  isLocalHypercover :
    (hypercoveringAugmentedPresheaf simplicial augmentation).IsLocalHypercover J

end Target

namespace HypercoveringOf

variable {J : GrothendieckTopology C} {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- A hypercovering coerces to its underlying simplicial semi-representable family. -/
instance instCoeToSimplicialObject :
    CoeOut (HypercoveringOf J 𝒢) (SimplicialObject (SR(C))) where
  coe H := H.simplicial

/-- The degree-`0` local-surjectivity property of a hypercovering. -/
theorem zero_locallySurjective (H : HypercoveringOf J 𝒢) :
    ZeroLocallySurjective J H.simplicial H.augmentation := sorry

/-- The degree-`1` local-surjectivity property of a hypercovering. -/
theorem one_locallySurjective (H : HypercoveringOf J 𝒢) :
    OneLocallySurjective J H.simplicial H.augmentation := sorry

/-- The higher matching-map local-surjectivity property of a hypercovering. -/
theorem higher_locallySurjective (H : HypercoveringOf J 𝒢) (n : ℕ) :
    HigherLocallySurjective J H.simplicial (n + 1) := sorry

/-- The degree-`0` augmentation map of a hypercovering. -/
abbrev zeroMap (H : HypercoveringOf J 𝒢) :
    (hypercoveringPresheaf H.simplicial).obj (op ⦋0⦌) ⟶ 𝒢 :=
  (hypercoveringAugmentedPresheaf H.simplicial H.augmentation).zeroMap

/-- The degree-`1` matching map of a hypercovering. -/
noncomputable abbrev oneMap (H : HypercoveringOf J 𝒢) :
    (hypercoveringPresheaf H.simplicial).obj (op ⦋1⦌) ⟶
      (pullback H.zeroMap H.zeroMap : Cᵒᵖ ⥤ Type (max w v)) :=
  (hypercoveringAugmentedPresheaf H.simplicial H.augmentation).oneMap

/-- The two degree-`1` face maps agree after composing with the degree-`0` map. -/
theorem oneMap_condition (H : HypercoveringOf J 𝒢) :
    Limits.FormalCoproduct.toPresheaf.map (H.simplicial.δ 0) ≫ H.zeroMap =
      Limits.FormalCoproduct.toPresheaf.map (H.simplicial.δ 1) ≫ H.zeroMap := sorry

/-- The higher matching map of a hypercovering. -/
noncomputable abbrev higherMap (H : HypercoveringOf J 𝒢) (n : ℕ) :
    (hypercoveringPresheaf H.simplicial).obj (op ⦋n + 1⦌) ⟶
      ((SimplicialObject.cosk n).obj (hypercoveringPresheaf H.simplicial)).obj
        (op ⦋n + 1⦌) :=
  SimplicialObject.matchingMap (hypercoveringPresheaf H.simplicial) n

end HypercoveringOf

end CategoryTheory
