module

public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import StacksCheckRecall

/-!
# The collection of hypercoverings

The reusable owner bundles the entire collection of hypercoverings of a fixed target as a Lean
type, rather than postulating a merely cofinal family of choices.
-/

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasPullbacks C] (X : C)

/- Lemma 25.3.7: all hypercoverings of a fixed object form a type in an explicit
successor-universe bound. -/
@[stacks 01G7] #check
  (inferInstance :
    Small.{max (u + 1) (v + 1) (w + 1)} (Hypercovering.{w} J X))

#check @Hypercovering.equivSubtype

end CategoryTheory
