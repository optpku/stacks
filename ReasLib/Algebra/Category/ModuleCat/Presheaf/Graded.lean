module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Basic
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer-graded tensor products of module-valued presheaves

Tensor products and colimits of module-valued presheaves are computed pointwise.  Consequently
tensoring preserves the coproducts that occur in integer-graded totalization.  This leaf records
the three coherence instances that are not inferred by Mathlib's generic graded-object API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace ModuleCat.Presheaf

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B]

/-- Pointwise right tensoring preserves the coproducts used by left-associated graded
totalization of module-valued presheaves. -/
@[stacks 06YU "module-presheaf left-associated graded tensor coherence"]
instance hasGoodTensor₁₂Tensor
    (G₁ G₂ G₃ : GradedObject ℤ (Presheaf C B)) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ := sorry

/-- Pointwise left tensoring preserves the coproducts used by right-associated graded
totalization of module-valued presheaves. -/
@[stacks 06YU "module-presheaf right-associated graded tensor coherence"]
instance hasGoodTensorTensor₂₃
    (G₁ G₂ G₃ : GradedObject ℤ (Presheaf C B)) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ := sorry

/-- Pointwise tensoring preserves the coproducts used in four-fold graded totalization of
module-valued presheaves. -/
@[stacks 06YU "module-presheaf four-fold graded tensor coherence"]
instance hasTensor₄ObjExt
    (G₁ G₂ G₃ G₄ : GradedObject ℤ (Presheaf C B)) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ := sorry

end ModuleCat.Presheaf
