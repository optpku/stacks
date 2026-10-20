module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Skeleton.Degreewise
import StacksCheckRecall

/-!
@stack 018M

# Lemma 14.21.2 compatibility facade

For a degree within the truncation range, the pointwise left Kan extension agrees canonically
with the original truncated object. The reusable owner is the truncated-simplex specialization
`SimplicialObject.Truncated.skeleton.degree.inRange.iso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory SimplexCategory.Truncated
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {m n : ℕ} (hn : n ≤ m) (U : SimplicialObject.Truncated C m)

/- Lemma 14.21.2: in a degree already present in the truncation, the skeleton colimit is
canonically isomorphic to the original degree-`n` object. -/
@[stacks 018M]
#check
  (SimplicialObject.Truncated.skeleton.degree.inRange.iso U hn :
    U.obj (op ⦋n, hn⦌ₘ) ≅
      colimit (SimplicialObject.Truncated.skeleton.degree.inRange.diagram U hn))

variable [U.HasPointwiseSkeleton]

/- The reusable compatibility bridge identifies this colimit coordinate with the component of
the objectwise left-Kan-extension unit. -/
@[stacks 018M "Lemma 14.21.2: compatibility with the left Kan extension unit"]
#check
  (SimplicialObject.Truncated.skeleton.degree.inRange.iso.unit U hn :
    (SimplicialObject.Truncated.skeleton.degree.inRange.iso U hn).hom ≫
        (SimplicialObject.Truncated.skeleton.degree.isoColimit U ⦋n⦌).inv =
      ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app
        (op ⦋n, hn⦌ₘ))

end CategoryTheory
