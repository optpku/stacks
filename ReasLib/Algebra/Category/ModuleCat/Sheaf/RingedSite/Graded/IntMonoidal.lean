/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer-graded tensor totalization on a ringed site

Coproducts give the total tensor product. Closedness gives preservation for left tensoring, while
braiding transports it to right tensoring. This leaf records exactly the four hypotheses consumed
by Mathlib's totalized monoidal structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.IntGraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [UnivLE.{max u v, z}]
variable {O : Sheaf J CommRingCat.{w}}
variable [MonoidalCategory (ringedSiteModuleCategory.{u, v, z, w} J O)]

/-- The total tensor product of two integer-graded module sheaves exists. -/
@[stacks 0FPB "integer-graded tensor totalization", instance]
theorem hasTensor
    (X Y : GradedObject ℤ (ringedSiteModuleCategory.{u, v, z, w} J O)) :
    GradedObject.HasTensor X Y := sorry

section Closed

/-- Left tensoring commutes with the coproducts used to totalize the last two factors. -/
@[stacks 0FP8 "right-associated totalization coherence", instance]
theorem hasGoodTensorTensor₂₃
    [MonoidalClosed (ringedSiteModuleCategory.{u, v, z, w} J O)]
    (X Y Z : GradedObject ℤ (ringedSiteModuleCategory.{u, v, z, w} J O)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := sorry

/-- Left tensoring commutes with the coproducts used in fourfold totalization. -/
@[stacks 0FP8 "fourfold totalization coherence", instance]
theorem hasTensor₄ObjExt
    [MonoidalClosed (ringedSiteModuleCategory.{u, v, z, w} J O)]
    (X Y Z W : GradedObject ℤ (ringedSiteModuleCategory.{u, v, z, w} J O)) :
    GradedObject.HasTensor₄ObjExt X Y Z W := sorry

end Closed

section BraidedClosed

/-- Right tensoring commutes with the coproducts used to totalize the first two factors. -/
@[stacks 0FP8 "left-associated totalization coherence", instance]
theorem hasGoodTensor₁₂Tensor
    [BraidedCategory (ringedSiteModuleCategory.{u, v, z, w} J O)]
    [MonoidalClosed (ringedSiteModuleCategory.{u, v, z, w} J O)]
    (X Y Z : GradedObject ℤ (ringedSiteModuleCategory.{u, v, z, w} J O)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := sorry

end BraidedClosed


end SheafOfModules.RingedSite.IntGraded
