module

public import ReasLib.AlgebraicTopology.SimplicialSet.KanFibration.Limits
import StacksCheckRecall

/-!
@stack 08NY
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v

namespace SSet.modelCategoryQuillen

variable {ι : Type v} {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
variable [HasProduct X] [HasProduct Y] [∀ i, Fibration (f i)]

/- Lemma 14.31.5 (08NY): products preserve Kan fibrations. -/
@[stacks 08NY]
#check (SSet.modelCategoryQuillen.fibration.piMap f : Fibration (Limits.Pi.map f))

end SSet.modelCategoryQuillen
