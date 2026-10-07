module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import ReasLib.CategoryTheory.MorphismProperty.Limits
import StacksCheckRecall

/-!
@stack 08NR
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

universe u w

namespace SSet.modelCategoryQuillen.I

variable {J : Type w} {X Y : J → SSet.{u}}
variable [HasProduct X] [HasProduct Y]
variable (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, I.rlp (f j))

/- Lemma 14.30.6 (08NR): products preserve the boundary-inclusion right lifting property. -/
@[stacks 08NR]
#check (MorphismProperty.IsStableUnderProductsOfShape.piMap f hf :
  I.rlp (Limits.Pi.map f))

end SSet.modelCategoryQuillen.I
