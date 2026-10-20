module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Augmentation
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Sheafification
import StacksCheckRecall

/-!
# Lemma 25.3.9 compatibility

A fixed-target hypercovering is first sent to the generic presheaf-target owner.  The three
source clauses are then the degree-zero, degree-one, and positive matching-map sheafification
properties of that owner.
-/

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}
variable [Limits.HasPullbacks C] [HasWeakSheafify J (Type (max w v))]
variable (K : Hypercovering.{w} J X)

/- Lemma 25.3.9 (1) [stacks 01G9]: the degree-`0` augmentation becomes locally surjective after
sheafification. -/
@[stacks 01G9 "(1)"] #check
  HypercoveringOf.Sheafification.zeroMap_locallySurjective K.toPresheafTarget

/- Lemma 25.3.9 (2) [stacks 01G9]: the degree-`1` matching map becomes locally surjective after
sheafification. -/
@[stacks 01G9 "(2)"] #check
  HypercoveringOf.Sheafification.oneMap_locallySurjective K.toPresheafTarget

/- Lemma 25.3.9 (3) [stacks 01G9]: for `1 ≤ n`, the degree-`n + 1` comparison with the
`n`-coskeleton becomes locally surjective after sheafification. -/
@[stacks 01G9 "(3)"] #check fun (n : ℕ) (hn : 1 ≤ n) ↦
  HypercoveringOf.Sheafification.higherMap_locallySurjective K.toPresheafTarget n hn

#check @Hypercovering.toPresheafTarget
#check @Presheaf.isLocallySurjective_presheafToSheaf_map_iff

end CategoryTheory
