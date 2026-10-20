module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.LocalHypercover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheafifying presheaf-target hypercoverings

Local surjectivity of the matching maps of a presheaf-target hypercovering passes to their
sheafifications. This leaf is the only part of the basic API that requires weak sheafification.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Sheafification

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max w v))]
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- Lemma 25.3.9 (1) (01G9), at the reusable presheaf-target level: the sheafification of the
degree-`0` augmentation of a hypercovering is locally surjective. -/
@[stacks 01G9 "(1)"]
theorem zeroMap_locallySurjective (H : HypercoveringOf J 𝒢) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map H.zeroMap) := sorry

/-- Lemma 25.3.9 (2) (01G9), at the reusable presheaf-target level: the sheafification of the
degree-`1` matching map of a hypercovering is locally surjective. -/
@[stacks 01G9 "(2)"]
theorem oneMap_locallySurjective (H : HypercoveringOf J 𝒢) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map H.oneMap) := sorry

/-- Lemma 25.3.9 (3) (01G9), at the reusable presheaf-target level: every positive matching map
of a hypercovering becomes locally surjective after sheafification. -/
@[stacks 01G9 "(3)"]
theorem higherMap_locallySurjective
    (H : HypercoveringOf J 𝒢) (n : ℕ) (hn : 1 ≤ n) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map (H.higherMap n)) := sorry

end CategoryTheory.HypercoveringOf.Sheafification
