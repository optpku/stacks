/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.InternalHom
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom of complexes on a ringed site

The strict product-valued internal Hom is built from the canonical local-Hom sheaves and
signed differential. Both its quasi-isomorphism theorem and its K-flat/K-injective criterion
use this fixed construction and the same canonical tensor product on module sheaves.
The legacy geometric namespace of `strictInternalHom` is retained for compatibility.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The actual product-valued cochain internal-Hom bifunctor on module sheaves. -/
def strictInternalHom :
    (CochainComplex (ringedSiteModuleCategory J O) ℤ)ᵒᵖ ⥤
      CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
        CochainComplex (ringedSiteModuleCategory J O) ℤ := by
  let tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let closed := @CochainComplex.InternalHom.monoidalClosed
    (ringedSiteModuleCategory J O)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
    preservesLeft preservesRight
  exact @MonoidalClosed.internalHom _ inferInstance _ closed

end RingedSite.Hom.ModuleDerived.InternalHom

namespace SheafOfModules.RingedSite.IHom

open RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Lemma 21.34.7 (0A95): the canonical sheaf internal-Hom map induced by
quasi-isomorphisms is a quasi-isomorphism when both targets are K-injective. -/
@[stacks 0A95 "quasi-isomorphism of internal-Hom complexes"]
theorem quasiIso_map
    {L' L I' I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    [CochainComplex.IsKInjective I'] [CochainComplex.IsKInjective I]
    (f : L' ⟶ L) (g : I' ⟶ I) (h_f : QuasiIso f) (h_g : QuasiIso g) :
    QuasiIso (((strictInternalHom.obj (op L)).map g) ≫
      (strictInternalHom.map f.op).app I) := sorry

/-- A K-flat source and a K-injective target have K-injective canonical sheaf internal Hom.
K-flatness uses the same canonical module-sheaf tensor as `strictInternalHom`. -/
@[stacks 0A96 "K-injectivity of internal-Hom complexes"]
theorem isKInjective_of_isKFlat
    {L I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (hL : L.IsKFlat) [I.IsKInjective] :
    ((strictInternalHom.obj (op L)).obj I).IsKInjective := by
  letI tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  letI goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  letI goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  letI tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  letI preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
      ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  letI preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
      ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  change (CategoryTheory.CochainComplex.InternalHom.obj L I).IsKInjective
  exact CategoryTheory.CochainComplex.InternalHom.isKInjective_of_isKFlat L I hL

end SheafOfModules.RingedSite.IHom

end
