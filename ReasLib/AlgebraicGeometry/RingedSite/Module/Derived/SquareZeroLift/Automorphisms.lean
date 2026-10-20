/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SquareZeroLift
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Automorphisms of square-zero lifts of derived modules

The shifted connecting morphism defines a boundary whose additive cokernel is canonically
the group of compatible automorphisms of a bounded-above lift.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor
open scoped DerivedExt

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, `DerivedTensor.Right.functor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): `monoidalCategory` is reducible to `KFlat.monoidalCategory` at the pinned `moduleCat_hasDerivedCategory`; `ρ_`, whiskering, `tensorLeft`, `mapUnitIso`, and the Ext target of `mapObstruction` must share that tensor.
attribute [local instance] monoidalCategory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]

variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}} (π : 𝒪 ⟶ 𝒪₀)
variable [Sheaf.IsLocallySurjective π]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))) (up ℤ)]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{w} (sameSiteHom π))
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [DerivedAdjunction.HasPair.{w} (sameSiteHom π)]
variable [KFlat.HomotopyTensorDescends 𝒪]
variable [KFlat.TensorDescends 𝒪]
variable [KFlat.IsLocalization 𝒪]
variable [KFlat.HomotopyTensorDescends 𝒪₀]
variable [KFlat.TensorDescends 𝒪₀]
variable [KFlat.IsLocalization 𝒪₀]
variable [Tensor.Has 𝒪₀]
variable [(tensorO0 π).OplaxMonoidal]
variable [(pushforwardO0 π).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)), (tensorLeft L).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w}
      (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)),
  IsIso ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)]
variable [IsIso (pushforwardSingleUnit π (unitModule J 𝒪₀))]

variable {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}

/-- The group of automorphisms of a lift whose derived reduction is the identity. -/
noncomputable abbrev Aut (L : Lift π h_sq K₀) : Type _ :=
  ((tensorO0 π).mapAut L.object).ker

/-- The kernel-triangle inclusion obtained by tensoring the kernel ideal inclusion. -/
noncomputable def kernelTensorInclusion
    (K : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    K ⊗ kernelSheafSingle π ⟶ K :=
  (K ◁ (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).map
      (KernelIdeal.ι π)) ≫
    (K ◁ (structureSheafSingle₀Iso (𝒪₀ := 𝒪)).hom) ≫ (ρ_ K).hom

/-- Tensoring the kernel ideal and applying the projection formula identifies the coefficient
map from a lift with derived restriction of its reduced kernel coefficient. -/
noncomputable def kernelTensorComparison (L : Lift π h_sq K₀) :
    L.object ⊗ kernelSheafSingle π ⟶
      (pushforwardO0 π).obj (K₀ ⊗ kernelIdeal0Single π h_sq) :=
  (L.object ◁ (kernelSheafSingleIso π h_sq).inv) ≫
    (L.object ◁ pushforwardSingleUnit π (kernelIdeal0 π h_sq)) ≫
    tensorPushforwardHom π L.object (kernelIdeal0Single π h_sq) ≫
    (pushforwardO0 π).map (L.iso.hom ▷ kernelIdeal0Single π h_sq)

/-- The adjunction mate of a kernel-valued map after identifying the reduction of a lift. -/
noncomputable def autAdjunct (L : Lift π h_sq K₀)
    (f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) :
    L.object ⟶ (pushforwardO0 π).obj (K₀ ⊗ kernelIdeal0Single π h_sq) :=
  (moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv L.object
    (K₀ ⊗ kernelIdeal0Single π h_sq) (L.iso.hom ≫ f)

/-- A compatible automorphism is identity plus a kernel-valued map whose comparison is the
adjunction mate of the given reduced map. -/
def autLiftRelation (L : Lift π h_sq K₀)
    (f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) (φ : Aut π h_sq L) : Prop :=
  ∃ g : L.object ⟶ L.object ⊗ kernelSheafSingle π,
    g ≫ kernelTensorComparison π h_sq L = autAdjunct π h_sq L f ∧
      φ.val.hom = 𝟙 L.object + g ≫ kernelTensorInclusion π L.object

/-- The boundary from negative first self-extensions to kernel-valued maps is obtained from
the shifted kernel-triangle connecting morphism by derived adjunction. -/
noncomputable def autDelta (L : Lift π h_sq K₀) :
    Ext⁽(-1 : ℤ)⁾(K₀, K₀) →+ (K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) :=
  AddMonoidHom.mk'
    (fun ξ ↦ L.iso.inv ≫
      ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv L.object
        (K₀ ⊗ kernelIdeal0Single π h_sq)).symm
        ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv L.object
            (K₀⟦(-1 : ℤ)⟧) (L.iso.hom ≫ ξ) ≫
          (pushforwardO0 π).map (L.iso.inv⟦(-1 : ℤ)⟧') ≫
          ((pushforwardO0 π).commShiftIso (-1 : ℤ)).hom.app ((tensorO0 π).obj L.object) ≫
          (connectingPushforward π h_sq L.object)⟦(-1 : ℤ)⟧' ≫
          ((pushforwardO0 π).commShiftIso (-1 : ℤ)).inv.app
            (((tensorO0 π).obj L.object ⊗ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧) ≫
          (pushforwardO0 π).map
            ((shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
              ((tensorO0 π).obj L.object ⊗ kernelIdeal0Single π h_sq)) ≫
          (pushforwardO0 π).map (L.iso.hom ▷ kernelIdeal0Single π h_sq)))
    sorry

/-- The boundary is the adjunction transport of the connecting morphism shifted by minus one,
with the successive coefficient shifts cancelled. -/
theorem autDelta_spec (L : Lift π h_sq K₀)
    (ξ : Ext⁽(-1 : ℤ)⁾(K₀, K₀)) :
    autDelta π h_sq L ξ =
      L.iso.inv ≫
      ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv L.object
        (K₀ ⊗ kernelIdeal0Single π h_sq)).symm
        ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv L.object
            (K₀⟦(-1 : ℤ)⟧) (L.iso.hom ≫ ξ) ≫
          (pushforwardO0 π).map (L.iso.inv⟦(-1 : ℤ)⟧') ≫
          ((pushforwardO0 π).commShiftIso (-1 : ℤ)).hom.app ((tensorO0 π).obj L.object) ≫
          (connectingPushforward π h_sq L.object)⟦(-1 : ℤ)⟧' ≫
          ((pushforwardO0 π).commShiftIso (-1 : ℤ)).inv.app
            (((tensorO0 π).obj L.object ⊗ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧) ≫
          (pushforwardO0 π).map
            ((shiftFunctorCompIsoId _ (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app
              ((tensorO0 π).obj L.object ⊗ kernelIdeal0Single π h_sq)) ≫
          (pushforwardO0 π).map (L.iso.hom ▷ kernelIdeal0Single π h_sq)) := sorry

/-- The additive cokernel of the negative first-extension boundary. -/
noncomputable abbrev autCoker (L : Lift π h_sq K₀) :=
  (K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) ⧸ (autDelta π h_sq L).range

/-- The automorphism group of a bounded-above lift is canonically the cokernel of the
negative first-extension boundary, characterized by adjunction and kernel inclusion. -/
theorem autEquiv (K₀ : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (L : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove) :
    ∃! e : Multiplicative (autCoker π h_sq L) ≃* Aut π h_sq L,
      ∀ f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq,
        autLiftRelation π h_sq L f (e (Multiplicative.ofAdd (Quotient.mk _ f))) := sorry

end

end RingedSite.Hom.ModuleDerived
