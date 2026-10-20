module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Symmetric
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric monoidal complexes of modules on a commutative ringed site

This is the direct import boundary for the canonical tensor product on module sheaves and its
Koszul totalization to cochain complexes.  Downstream files only need to assume a closed structure
on the complex category; its monoidal and symmetric structures are inferred here.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite (ringedSiteModuleCategory ringSheaf)

noncomputable section

universe u v w

namespace RingedSite.CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})

namespace IntGraded

/-- Right tensoring commutes with the coproducts used in left-associated integer-graded
totalization over `O`. -/
@[stacks 0FP8 "commutative ringed-site left-associated totalization coherence", instance]
theorem hasGoodTensor₁₂Tensor
    (X Y Z : GradedObject ℤ (ringedSiteModuleCategory.{u, v, w, w} J O)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := sorry

/-- Left tensoring commutes with the coproducts used in right-associated integer-graded
totalization over `O`. -/
@[stacks 0FP8 "commutative ringed-site right-associated totalization coherence", instance]
theorem hasGoodTensorTensor₂₃
    (X Y Z : GradedObject ℤ (ringedSiteModuleCategory.{u, v, w, w} J O)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := sorry

/-- Left tensoring commutes with the coproducts used in fourfold integer-graded totalization
over `O`. -/
@[stacks 0FP8 "commutative ringed-site fourfold totalization coherence", instance]
theorem hasTensor₄ObjExt
    (X Y Z W : GradedObject ℤ (ringedSiteModuleCategory.{u, v, w, w} J O)) :
    GradedObject.HasTensor₄ObjExt X Y Z W := sorry

/-- Left-associated totalization coherence in the direct `over` presentation of a slice
ringed site. -/
@[stacks 03L6 "slice-site left-associated totalization coherence", instance]
theorem moduleOverHasGoodTensor₁₂Tensor (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (X Y Z : GradedObject ℤ (SheafOfModules.{w} ((ringSheaf J O).over U))) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := sorry

/-- Right-associated totalization coherence in the direct `over` presentation of a slice
ringed site. -/
@[stacks 03L6 "slice-site right-associated totalization coherence", instance]
theorem moduleOverHasGoodTensorTensor₂₃ (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (X Y Z : GradedObject ℤ (SheafOfModules.{w} ((ringSheaf J O).over U))) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := sorry

/-- Fourfold totalization coherence in the direct `over` presentation of a slice ringed site. -/
@[stacks 03L6 "slice-site fourfold totalization coherence", instance]
theorem moduleOverHasTensor₄ObjExt (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (X Y Z W : GradedObject ℤ (SheafOfModules.{w} ((ringSheaf J O).over U))) :
    GradedObject.HasTensor₄ObjExt X Y Z W := sorry

end IntGraded

end RingedSite.CochainComplex
