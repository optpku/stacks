module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
import StacksCheckRecall

/-!
@stack 0181
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {n : ℕ}
variable [SimplicialObject.Truncated.HasCoskeletons C n]
variable (U : SimplicialObject C) (V : SimplicialObject.Truncated C n)

/- Equation 14.19.0.1 is the Hom-set equivalence of the truncation-coskeleton adjunction,
oriented as in the source. -/
@[stacks 0181 "Equation 14.19.0.1"]
#check (((coskAdj n).homEquiv U V).symm :
  (U ⟶ (SimplicialObject.Truncated.cosk n).obj V) ≃
    ((SimplicialObject.truncation n).obj U ⟶ V))

end CategoryTheory
