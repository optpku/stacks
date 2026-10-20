module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula

/-!
# Obstruction class of a map of complexes along a square-zero kernel

On a site, a locally surjective square-zero map of ring sheaves determines a connecting
morphism in `D(𝒪₀)` after derived extension of scalars. Postcomposition with that connecting
morphism is the canonical obstruction class of a map `α₀ : K₀ ⟶ L₀`.
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

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, `DerivedTensor.Right.functor`, `DerivedTensor.Left.functor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
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
variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}}

variable (π : 𝒪 ⟶ 𝒪₀)
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
variable [@DerivedTensor.Right.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Right.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{w} (sameSiteHom π))
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf J 𝒪₀))]
variable [DerivedAdjunction.HasPair.{w} (sameSiteHom π)]
variable [KFlat.HomotopyTensorDescends 𝒪]
variable [KFlat.TensorDescends 𝒪]
variable [KFlat.IsLocalization 𝒪]
variable [KFlat.HomotopyTensorDescends 𝒪₀]
variable [KFlat.TensorDescends 𝒪₀]
variable [KFlat.IsLocalization 𝒪₀]
variable [Tensor.Has 𝒪₀]

/-- Derived extension of scalars along `π`, sending `K` to `K ⊗ᴸ 𝒪₀`. -/
noncomputable abbrev tensorO0 :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) ⥤
      ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  SheafOfModules.RingedSite.SameSite.pullbackDerived π

/-- The kernel ideal of `π`, regarded as an `𝒪₀`-module via the square-zero descent. -/
noncomputable abbrev kernelIdeal0 : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  KernelIdeal.IsSquareZero.targetModule h_sq inferInstance

/-- The degree-zero single of the descended kernel ideal. -/
noncomputable abbrev kernelIdeal0Single :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (0 : ℤ)).obj
    (kernelIdeal0 π h_sq)

/-- Restriction of scalars along `π` as a functor of unbounded derived categories. -/
noncomputable abbrev pushforwardO0 :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) ⥤
      ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  modulePushforwardDerived.{w} (sameSiteHom π)

variable [(tensorO0 π).OplaxMonoidal]
variable [(pushforwardO0 π).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)), (tensorLeft L).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w}
      (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)),
  IsIso ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)]

/-- The short complex `ℐ ⟶ 𝒪 ⟶ π_* 𝒪₀` of `𝒪`-modules. -/
noncomputable def kernelModuleShortComplex :
    ShortComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :=
  ShortComplex.mk (KernelIdeal.ι π) (KernelIdeal.map π) (KernelIdeal.ι_comp_map π)

/-- A locally surjective map of ring sheaves yields a short exact kernel sequence of
`𝒪`-modules. -/
theorem kernelModule_shortExact : (kernelModuleShortComplex π).ShortExact where
  exact := (kernelModuleShortComplex π).exact_of_f_is_kernel
    (CategoryTheory.Limits.KernelFork.IsLimit.ofι _ _
      (fun k hk => CategoryTheory.Limits.factorThruKernelSubobject (KernelIdeal.map π) k hk)
      (fun k hk => CategoryTheory.Limits.factorThruKernelSubobject_comp_arrow _ k hk)
      (fun k hk l hl => (cancel_mono (KernelIdeal.ι π)).1
        (hl.trans (CategoryTheory.Limits.factorThruKernelSubobject_comp_arrow _ k hk).symm)))
  mono_f := by
    change Mono (KernelIdeal.ι π)
    infer_instance
  epi_g := by
    apply (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).epi_of_epi_map
    change Epi ((sheafCompose J (forget CommRingCat.{w})).map π)
    infer_instance

/-- The connecting morphism of `kernelModuleShortComplex` in `D(𝒪)`. -/
noncomputable def kernelConnecting :
    (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
        ((sameSiteHom π).modulePushforward.{w}.obj (unitModule J 𝒪₀)) ⟶
      ((singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
        (KernelIdeal.sheaf π))⟦(1 : ℤ)⟧ :=
  (kernelModule_shortExact π).singleδ

/-- The degree-zero single of the kernel ideal as an `𝒪`-module. -/
noncomputable abbrev kernelSheafSingle :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
    (KernelIdeal.sheaf π)

/-- The underlying additive comparison from the restricted square-zero kernel module to the
kernel ideal sheaf. -/
noncomputable def kernelIdealRestrictToPresheaf :
    ((sameSiteHom π).modulePushforward.{w}.obj (kernelIdeal0 π h_sq)).val.presheaf ⟶
      (KernelIdeal.sheaf π).val.presheaf :=
  (h_sq.targetModuleForgetIso inferInstance).hom.hom

/-- The inverse underlying additive comparison from the kernel ideal sheaf to the restricted
square-zero kernel module. -/
noncomputable def kernelIdealRestrictInvToPresheaf :
    (KernelIdeal.sheaf π).val.presheaf ⟶
      ((sameSiteHom π).modulePushforward.{w}.obj (kernelIdeal0 π h_sq)).val.presheaf :=
  (h_sq.targetModuleForgetIso inferInstance).inv.hom

/-- The underlying additive comparison `kernelIdealRestrictToPresheaf` is linear over `𝒪`. -/
theorem kernelIdealRestrictToPresheaf_smul (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪).obj.obj U)
    (m : ((sameSiteHom π).modulePushforward.{w}.obj (kernelIdeal0 π h_sq)).val.obj U) :
    (kernelIdealRestrictToPresheaf π h_sq).app U (r • m) =
      r • (kernelIdealRestrictToPresheaf π h_sq).app U m := sorry

/-- The inverse underlying additive comparison is linear over `𝒪`. -/
theorem kernelIdealRestrictInvToPresheaf_smul (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪).obj.obj U)
    (m : (KernelIdeal.sheaf π).val.obj U) :
    (kernelIdealRestrictInvToPresheaf π h_sq).app U (r • m) =
      r • (kernelIdealRestrictInvToPresheaf π h_sq).app U m := sorry

/-- Restriction of scalars of the square-zero kernel module recovers the kernel ideal sheaf. -/
noncomputable def kernelIdealRestrictIso :
    (sameSiteHom π).modulePushforward.{w}.obj (kernelIdeal0 π h_sq) ≅
      KernelIdeal.sheaf π where
  hom := ⟨PresheafOfModules.homMk
    (kernelIdealRestrictToPresheaf π h_sq) (kernelIdealRestrictToPresheaf_smul π h_sq)⟩
  inv := ⟨PresheafOfModules.homMk
    (kernelIdealRestrictInvToPresheaf π h_sq) (kernelIdealRestrictInvToPresheaf_smul π h_sq)⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The degree-zero single of `kernelIdealRestrictIso`. -/
noncomputable def kernelSheafSingleIso :
    (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
        ((sameSiteHom π).modulePushforward.{w}.obj (kernelIdeal0 π h_sq)) ≅
      kernelSheafSingle π :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).mapIso
    (kernelIdealRestrictIso π h_sq)

/-- Comparison `π_* M[0] ⟶ Rπ_* (M[0])` from the underived degree-zero single to derived
restriction of scalars. -/
noncomputable def pushforwardSingleUnit
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) :
    (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
        ((sameSiteHom π).modulePushforward.{w}.obj M) ⟶
      (pushforwardO0 π).obj
        ((singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
          (0 : ℤ)).obj M) :=
  Q.map ((HomologicalComplex.singleMapHomologicalComplex
      (sameSiteHom π).modulePushforward.{w} (up ℤ) (0 : ℤ)).inv.app M) ≫
    ((modulePushforwardToDerived.{w} (sameSiteHom π)).totalRightDerivedUnit
      (moduleLocalization.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))).app
      ((HomotopyCategory.singleFunctor
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (0 : ℤ)).obj M)

variable [IsIso (pushforwardSingleUnit π (unitModule J 𝒪₀))]

/-- The kernel connecting morphism transported to the shifted derived restriction of the
descended kernel ideal. -/
noncomputable def kernelConnecting_toShiftedPushforward :
    (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
        ((sameSiteHom π).modulePushforward.{w}.obj (unitModule J 𝒪₀)) ⟶
      ((pushforwardO0 π).obj (kernelIdeal0Single π h_sq))⟦(1 : ℤ)⟧ :=
  kernelConnecting π ≫
    (shiftFunctor _ (1 : ℤ)).map (kernelSheafSingleIso π h_sq).inv ≫
    (shiftFunctor _ (1 : ℤ)).map (pushforwardSingleUnit π (kernelIdeal0 π h_sq))

/-- The derived structure sheaf of `𝒪`, as a degree-zero single. -/
noncomputable abbrev structureSheafSingle :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (0 : ℤ)).obj (unitModule J 𝒪)

/-- The derived structure sheaf of `𝒪₀`, as a degree-zero single. -/
noncomputable abbrev structureSheafSingle₀ :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (0 : ℤ)).obj (unitModule J 𝒪₀)

/-- Canonical identification of `𝒪₀[0]` with the K-flat derived tensor unit of `D(𝒪₀)`.
The forward map is the degree-zero single of `unitIsoTensorUnit`, transported along the
single/`Q` comparison, the homological-complex tensor unit, and `KFlat.mapUnitIso`. -/
noncomputable def structureSheafSingle₀Iso :
    structureSheafSingle₀ ≅
      𝟙_ (ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (0 : ℤ)).mapIso
      unitIsoTensorUnit ≪≫
    (singleFunctorIsoCompQ
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (0 : ℤ)).app
      (𝟙_ (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) ≪≫
    (quotientCompQhIso
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))).symm.app
      (HomologicalComplex.tensorUnit
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (up ℤ)) ≪≫
    CategoryTheory.DerivedCategory.KFlat.mapUnitIso.symm

/-- The forward map of `structureSheafSingle₀Iso` is the single of `unitIsoTensorUnit`
followed by the derived-tensor unit comparison. -/
theorem structureSheafSingle₀Iso_hom :
    structureSheafSingle₀Iso.hom =
      ((singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
          (0 : ℤ)).mapIso unitIsoTensorUnit).hom ≫
        (singleFunctorIsoCompQ
            (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (0 : ℤ)).hom.app
          (𝟙_ (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) ≫
        (quotientCompQhIso
            (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))).inv.app
          (HomologicalComplex.tensorUnit
            (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (up ℤ)) ≫
        CategoryTheory.DerivedCategory.KFlat.mapUnitIso.inv := sorry

/-- The kernel connecting morphism of `π`, transported to derived restriction of scalars of
`𝒪₀[0]`. -/
noncomputable def kernelConnectingPushforward :
    (pushforwardO0 π).obj structureSheafSingle₀ ⟶
      ((pushforwardO0 π).obj (kernelIdeal0Single π h_sq))⟦(1 : ℤ)⟧ :=
  CategoryTheory.inv (pushforwardSingleUnit π (unitModule J 𝒪₀)) ≫
    kernelConnecting_toShiftedPushforward π h_sq

/-- The comparison `L ⊗ π_* 𝒪₀[0] ⟶ π_* (L₀ ⊗ 𝒪₀[0])` from the projection formula. -/
noncomputable abbrev tensorPushforwardHom
    (L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) :
    L ⊗ (pushforwardO0 π).obj M ⟶
      (pushforwardO0 π).obj ((tensorO0 π).obj L ⊗ M) :=
  (moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M

/-- Inverse of `tensorPushforwardHom`, from the same-site projection-formula isomorphism. -/
noncomputable def tensorPushforwardInv
    (L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) :
    (pushforwardO0 π).obj ((tensorO0 π).obj L ⊗ M) ⟶
      L ⊗ (pushforwardO0 π).obj M :=
  CategoryTheory.inv
    ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)

/-- The connecting morphism `π_* L₀ ⟶ π_* ((L₀ ⊗ ℐ)⟦1⟧)` obtained by transporting
`L ⊗ kernelConnecting` along the projection-formula comparison and the shift comparison of
derived restriction of scalars. -/
noncomputable def connectingPushforward
    (L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    (pushforwardO0 π).obj ((tensorO0 π).obj L) ⟶
      (pushforwardO0 π).obj
        ((((tensorO0 π).obj L) ⊗ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧) :=
  (pushforwardO0 π).map (ρ_ ((tensorO0 π).obj L)).inv ≫
    (pushforwardO0 π).map (((tensorO0 π).obj L) ◁ structureSheafSingle₀Iso.inv) ≫
      tensorPushforwardInv π L structureSheafSingle₀ ≫
        (L ◁ kernelConnectingPushforward π h_sq) ≫
        ((tensorLeft L).commShiftIso (1 : ℤ)).hom.app
          ((pushforwardO0 π).obj (kernelIdeal0Single π h_sq)) ≫
          (shiftFunctor _ (1 : ℤ)).map
            (tensorPushforwardHom π L (kernelIdeal0Single π h_sq)) ≫
            ((pushforwardO0 π).commShiftIso (1 : ℤ)).inv.app _

/-- The canonical obstruction class `o(α₀)` in `Ext⁽1⁾(K₀, L₀ ⊗ ℐ)`, realized as the adjunction
mate of the composite of the derived unit, the pushforward of `α₀`, and
`connectingPushforward`. -/
noncomputable def mapObstruction
    {K L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (α₀ : (tensorO0 π).obj K ⟶ (tensorO0 π).obj L) :
    Ext⁽(1 : ℤ)⁾((tensorO0 π).obj K,
      (tensorO0 π).obj L ⊗ kernelIdeal0Single π h_sq) :=
  ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv K
      (((tensorO0 π).obj L ⊗ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧)).symm
    ((moduleDerivedAdjunction.{w} (sameSiteHom π)).unit.app K ≫
      (pushforwardO0 π).map α₀ ≫ connectingPushforward π h_sq L)

/-- `mapObstruction` is the adjunction mate of the composite
`K ⟶ π_* K₀ ⟶α₀ π_* L₀ ⟶ π_* ((L₀ ⊗ ℐ)⟦1⟧)` in `D(𝒪)`. -/
theorem mapObstruction_spec
    {K L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (α₀ : (tensorO0 π).obj K ⟶ (tensorO0 π).obj L) :
    ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv K
        (((tensorO0 π).obj L ⊗ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧))
      (mapObstruction π h_sq α₀) =
      (moduleDerivedAdjunction.{w} (sameSiteHom π)).unit.app K ≫
        (pushforwardO0 π).map α₀ ≫ connectingPushforward π h_sq L := sorry

/-- The obstruction class of a map obtained by derived extension of scalars vanishes. -/
theorem mapObstruction_zero_of_tensorO0Map
    {K L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (α : K ⟶ L) :
    mapObstruction π h_sq ((tensorO0 π).map α) = 0 := sorry

/-- Derived extension of scalars along `π` preserves cohomological boundedness above. -/
theorem pullbackDerived_isLE
    {K : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)} {a : ℤ} :
    K.IsLE a → ((tensorO0 π).obj K).IsLE a := sorry

/-- For bounded-above derived modules over a square-zero extension, the canonical obstruction
to lifting a morphism between their derived reductions vanishes exactly when a lift exists. -/
theorem mapObstruction_eq_zero_iff
    {K L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)} {a b : ℤ}
    [K.IsLE a] [L.IsLE b]
    (α₀ : (tensorO0 π).obj K ⟶ (tensorO0 π).obj L) :
    mapObstruction π h_sq α₀ = 0 ↔
      ∃ α : K ⟶ L, (tensorO0 π).map α = α₀ := sorry

end

end RingedSite.Hom.ModuleDerived

