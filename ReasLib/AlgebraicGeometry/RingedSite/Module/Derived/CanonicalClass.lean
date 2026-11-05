/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor

/-!
# Canonical class of a bounded-above complex on a square-zero ringed site

Along a locally surjective square-zero map `π : 𝒪 ⟶ 𝒪₀` of ring sheaves with kernel ideal `ℐ`,
every `K₀` in `D⁻(𝒪₀)` has a canonical morphism `ω(K₀) : K₀ ⟶ (K₀ ⊗ᴸ ℐ[0])⟦2⟧` in `D(𝒪₀)`.
A bounded-above representative is lifted
to a successive family of flat `𝒪`-modules assembled as coproducts of `j_! 𝒪_U` on local
sections, the failure `d ∘ d` is factored through `ℐ`, and the resulting chain map of the
extended complex is transported along the quasi-isomorphism and the K-flat identification.
-/

public section

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open HomologicalComplex
open Opposite
open SheafOfModules
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): RingedSiteDerived fixes the standard derived category, while Q, singleFunctor, and the derived-tensor interfaces have a free HasDerivedCategory parameter; this registration selects that same standard presentation.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

/-- Degree identity `n + 1 + 1 = n + 2`. -/
private def int_succ_succ (n : ℤ) : n + 1 + 1 = n + 2 :=
  (add_assoc n 1 1).trans (congrArg (HAdd.hAdd n) one_add_one_eq_two)

/-- Offset conversion `a + 1 - (k + 1) = (a + 1 - k) - 1`. -/
private def int_offset_succ (a : ℤ) (k : ℕ) : a + 1 - (k + 1 : ℕ) = (a + 1 - k) - 1 :=
  (congrArg (fun z : ℤ ↦ a + 1 - z) (Nat.cast_succ k)).trans
    (sub_add_eq_sub_sub (a + 1) (k : ℤ) 1)

/-- Recovering a cohomological degree from its `ℕ`-offset below `a + 1`. -/
private def int_offset_to_degree (a n : ℤ) (hn : n ≤ a + 1) :
    a + 1 - (a + 1 - n).toNat = n :=
  (congrArg (fun z : ℤ ↦ a + 1 - z) (Int.toNat_of_nonneg (sub_nonneg.mpr hn))).trans
    (sub_sub_cancel (a + 1) n)

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
variable [(restrictionAlong π).IsRightAdjoint]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [SheafOfModules.Localization.HasLowerShriek.{w} (ringSheaf J 𝒪)]
variable [DerivedTensor.Right.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]
variable [DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]

/-- The kernel ideal of `π`, regarded as an `𝒪₀`-module via square-zero descent. -/
noncomputable abbrev kernelIdeal0 :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀ :=
  KernelIdeal.IsSquareZero.targetModule h_sq inferInstance

/-- The degree-zero single of the descended kernel ideal in `D(𝒪₀)`. -/
noncomputable abbrev kernelIdeal0Single :
    RingedSiteDerived.{u, v, w, w} J 𝒪₀ :=
  (singleFunctor (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) (0 : ℤ)).obj
    (kernelIdeal0 π h_sq)

/-- The cochain complex `ℐ[0]` associated to the descended kernel ideal. -/
private noncomputable abbrev kernelIdeal0SingleComplex :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ :=
  (HomologicalComplex.single
      (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) (up ℤ) (0 : ℤ)).obj
    (kernelIdeal0 π h_sq)

/-- The shifted derived tensor `(K₀ ⊗ᴸ ℐ[0])⟦2⟧`. -/
noncomputable abbrev tensorKernelShift
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀) :
    RingedSiteDerived.{u, v, w, w} J 𝒪₀ :=
  (K₀ ⊗ᴸ kernelIdeal0Single π h_sq)⟦(2 : ℤ)⟧

/-- The map `(α ⊗ᴸ id_{ℐ[0]})⟦2⟧` induced by a morphism of derived `𝒪₀`-modules. -/
noncomputable def tensorKernelShiftMap
    {K₀ L₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀}
    (α : K₀ ⟶ L₀) :
    tensorKernelShift π h_sq K₀ ⟶ tensorKernelShift π h_sq L₀ :=
  (shiftFunctor _ (2 : ℤ)).map
    ((DerivedTensor.Right.functor (kernelIdeal0Single π h_sq)).map α)

section

omit [(restrictionAlong π).IsRightAdjoint]
  [SheafOfModules.Localization.HasLowerShriek.{w} (ringSheaf J 𝒪)]
  [DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]

/-- The shifted derived tensor map preserves identity morphisms. -/
@[simp]
theorem tensorKernelShiftMap_id
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀) :
    tensorKernelShiftMap π h_sq (𝟙 K₀) = 𝟙 (tensorKernelShift π h_sq K₀) := by
  simp only [tensorKernelShiftMap, CategoryTheory.Functor.map_id]

/-- The shifted derived tensor map preserves composition. -/
theorem tensorKernelShiftMap_comp
    {K₀ L₀ M₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀}
    (α : K₀ ⟶ L₀) (β : L₀ ⟶ M₀) :
    tensorKernelShiftMap π h_sq (α ≫ β) =
      tensorKernelShiftMap π h_sq α ≫ tensorKernelShiftMap π h_sq β := by
  simp only [tensorKernelShiftMap, CategoryTheory.Functor.map_comp]

end

/-- A chosen integer witnessing that a derived object is cohomologically bounded above. -/
private def isBoundedAboveBound
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) : ℤ :=
  Classical.choose hK

/-- The chosen bound of `isBoundedAboveBound` witnesses `IsLE`. -/
private instance instIsLE_isBoundedAboveBound
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    K₀.IsLE (isBoundedAboveBound K₀ hK) :=
  Classical.choose_spec hK

/-- A chosen preimage of a cohomologically bounded-above object remains bounded above. -/
private instance instObjPreimage_isLE
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀) {n : ℤ}
    [K₀.IsLE n] :
    (DerivedCategory.Q.objPreimage K₀).IsLE n :=
  (DerivedCategory.isLE_Q_obj_iff (DerivedCategory.Q.objPreimage K₀) n).mp
    (DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.Q.objObjPreimageIso K₀).symm n)

/-- A strictly bounded-above cochain representative of a derived object of `D⁻(𝒪₀)`. -/
private noncomputable def boundedRepresentative
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ :=
  (DerivedCategory.Q.objPreimage K₀).truncLE (isBoundedAboveBound K₀ hK)

/-- The chosen bounded-above representative is strictly supported in degrees at most the bound. -/
private instance instBoundedRepresentative_isStrictlyLE
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    (boundedRepresentative K₀ hK).IsStrictlyLE (isBoundedAboveBound K₀ hK) :=
  inferInstanceAs
    (((DerivedCategory.Q.objPreimage K₀).truncLE (isBoundedAboveBound K₀ hK)).IsStrictlyLE
      (isBoundedAboveBound K₀ hK))

/-- Pairs `(U, s)` of a site object in universe `w` and a local section of an `𝒪`-module. -/
private def localSectionIndex
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :=
  Σ U : C, (M.val.obj (op U) : Type w)



/-- Coproduct of `j_! 𝒪_U` indexed by all local sections of `M`. -/
private noncomputable def sectionCoproduct
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  @sigmaObj (localSectionIndex M) (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)
    inferInstance (fun i : localSectionIndex M ↦ SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) i.1)
    (by
      refine @HasColimitsOfShape.has_colimit _ _ _ _
        (@HasColimitsOfShape.of_small.{w, w} _ _ inferInstance
          (Discrete (localSectionIndex M)) _ ?_ inferInstance)
        (Discrete.functor (fun i : localSectionIndex M ↦ SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) i.1))
      exact @small_map _ _
        (@small_sigma C (fun U : C ↦ (M.val.obj (op U) : Type w))
          (@Small.trans_univLE.{max u v, w, u} C (small_max.{v} C) inferInstance)
          (fun _ ↦ inferInstance)) discreteEquiv)

/-- The summand map `j_{U!} 𝒪_U ⟶ M` sending the universal section to `s`. -/
private noncomputable def structureSummandHom
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪)
    (i : localSectionIndex M) :
    SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) i.1 ⟶ M :=
  (SheafOfModules.Localization.structureModuleHomEquiv (ringSheaf J 𝒪) i.1 M).symm i.2

/-- Evaluation of the local-section coproduct on `M`. -/
private noncomputable def sectionCoproductHom
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    sectionCoproduct M ⟶ M :=
  @Sigma.desc (localSectionIndex M) (ringedSiteModuleCategory.{u, v, w, w} J 𝒪)
    inferInstance (fun i : localSectionIndex M ↦ SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) i.1)
    (by
      refine @HasColimitsOfShape.has_colimit _ _ _ _
        (@HasColimitsOfShape.of_small.{w, w} _ _ inferInstance
          (Discrete (localSectionIndex M)) _ ?_ inferInstance)
        (Discrete.functor (fun i : localSectionIndex M ↦ SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) i.1))
      exact @small_map _ _
        (@small_sigma C (fun U : C ↦ (M.val.obj (op U) : Type w))
          (@Small.trans_univLE.{max u v, w, u} C (small_max.{v} C) inferInstance)
          (fun _ ↦ inferInstance)) discreteEquiv) M (structureSummandHom M)


/-- The adjunction unit of extension/restriction along `π`. -/
private noncomputable abbrev extendRestrictUnit
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    M ⟶ (restrictionAlong π).obj
      ((ChangeOfRings.extendScalars (ringSheafMap π)).obj M) :=
  (ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).unit.app M

/-- Restriction of a successive differential of `K` to an `𝒪`-module morphism. -/
private noncomputable def restrictedDiff
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ) :
    (restrictionAlong π).obj (K.X (e - 1)) ⟶ (restrictionAlong π).obj (K.X e) :=
  (restrictionAlong π).map
    (K.d (e - 1) (e - 1 + 1) ≫ eqToHom (congrArg K.X (sub_add_cancel e 1)))

/-- Cycles in a lifted term that map to boundaries in `K`, as an `𝒪`-module pullback. -/
private noncomputable def cycleBoundaryPullback
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  pullback (kernel.ι (dOut ≫ extendRestrictUnit π Fprev) ≫ toK) (restrictedDiff π K e)

/-- Kernel of `π_* (K^{e - 1} ⟶ K^e)`, whose local sections give a cycle-covering summand. -/
private noncomputable def homologyKernelRestrict
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  kernel (restrictedDiff π K e)

/-- The B-summand of the next lifted term is the local-section coproduct of the cycle pullback. -/
private noncomputable def liftSummandB
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  sectionCoproduct (cycleBoundaryPullback π K e dOut toK)

/-- The C-summand of the next lifted term is the local-section coproduct of homology cycles. -/
private noncomputable def liftSummandC
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  sectionCoproduct (homologyKernelRestrict π K e)

/-- The B-summand map into the previous lifted term. -/
private noncomputable def liftSummandBToPrev
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSummandB π K e dOut toK ⟶ F :=
  sectionCoproductHom (cycleBoundaryPullback π K e dOut toK) ≫
    pullback.fst (kernel.ι (dOut ≫ extendRestrictUnit π Fprev) ≫ toK)
      (restrictedDiff π K e) ≫
    kernel.ι (dOut ≫ extendRestrictUnit π Fprev)

/-- The B-summand comparison into `π_* K^{e - 1}`. -/
private noncomputable def liftSummandBToK
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSummandB π K e dOut toK ⟶ (restrictionAlong π).obj (K.X (e - 1)) :=
  sectionCoproductHom (cycleBoundaryPullback π K e dOut toK) ≫
    pullback.snd (kernel.ι (dOut ≫ extendRestrictUnit π Fprev) ≫ toK)
      (restrictedDiff π K e)

/-- The C-summand comparison into `π_* K^{e - 1}`. -/
private noncomputable def liftSummandCToK
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ) :
    liftSummandC π K e ⟶ (restrictionAlong π).obj (K.X (e - 1)) :=
  sectionCoproductHom (homologyKernelRestrict π K e) ≫ kernel.ι (restrictedDiff π K e)

/-- The direct sum `B ⊞ C` of the boundary-killing and cycle-covering modules. -/
private noncomputable def liftSuccX
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  liftSummandB π K e dOut toK ⊞ liftSummandC π K e

/-- Outgoing differential of the successor term onto the previous lifted module. -/
private noncomputable def liftSuccDOut
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSuccX π K e dOut toK ⟶ F :=
  biprod.desc (liftSummandBToPrev π K e dOut toK) 0

/-- Comparison of the successor term into `π_* K^{e - 1}`. -/
private noncomputable def liftSuccToK
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (e : ℤ)
    {F Fprev : ringedSiteModuleCategory.{u, v, w, w} J 𝒪}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSuccX π K e dOut toK ⟶ (restrictionAlong π).obj (K.X (e - 1)) :=
  biprod.desc (liftSummandBToK π K e dOut toK) (liftSummandCToK π K e)

/-- One degree of the recursive flat lift: a flat `𝒪`-module assembled from `j_! 𝒪_U`, its comparison
to `K`, and the outgoing differential onto the previous stage. -/
private def FlatLiftStage
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) (k : ℕ) :=
  Σ F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪,
    Σ Fpred : ringedSiteModuleCategory.{u, v, w, w} J 𝒪,
      (F ⟶ (restrictionAlong π).obj (K.X (a + 1 - k))) × (F ⟶ Fpred)

namespace FlatLiftStage

/-- The `𝒪`-module `F^{a + 1 - k}` of a recursive lift stage. -/
private def F
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ}
    {a : ℤ} {k : ℕ} (s : FlatLiftStage π K a k) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  s.1

/-- The previous module of a recursive lift stage. -/
private def Fpred
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ}
    {a : ℤ} {k : ℕ} (s : FlatLiftStage π K a k) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  s.2.1

/-- The comparison `F^{a + 1 - k} ⟶ π_* K^{a + 1 - k}` of a recursive lift stage. -/
private def toK
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ}
    {a : ℤ} {k : ℕ} (s : FlatLiftStage π K a k) :
    F π s ⟶ (restrictionAlong π).obj (K.X (a + 1 - k)) :=
  s.2.2.1

/-- The outgoing differential from a recursive lift stage to its previous module. -/
private def dOut
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ}
    {a : ℤ} {k : ℕ} (s : FlatLiftStage π K a k) :
    F π s ⟶ Fpred π s :=
  s.2.2.2

/-- The vanishing stage in degrees `> a`. -/
private def zero
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) : FlatLiftStage π K a 0 :=
  ⟨0, 0, 0, 0⟩

/-- One inductive step of the recursive flat lift, taking `F^{e - 1} = B ⊞ C`. -/
private def succ
    {K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ}
    {a : ℤ} {k : ℕ} (prev : FlatLiftStage π K a k) :
    FlatLiftStage π K a (k + 1) :=
  ⟨liftSuccX π K (a + 1 - k) (dOut π prev) (toK π prev),
    F π prev,
    liftSuccToK π K (a + 1 - k) (dOut π prev) (toK π prev) ≫
      eqToHom (congrArg ((restrictionAlong π).obj ∘ K.X) (int_offset_succ a k).symm),
    liftSuccDOut π K (a + 1 - k) (dOut π prev) (toK π prev)⟩

end FlatLiftStage

/-- Termwise recursive flat lift data in offset `k` below the bound. -/
private noncomputable def flatLiftStage
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) (k : ℕ) : FlatLiftStage π K a k :=
  Nat.rec (motive := fun n ↦ FlatLiftStage π K a n)
    (FlatLiftStage.zero π K a) (fun _ prev ↦ FlatLiftStage.succ π prev) k

/-- The recursive successive flat lift of a bounded-above complex, as `𝒪`-modules `F^{a + 1 - k}`. -/
private noncomputable def flatLiftX
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) (k : ℕ) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  FlatLiftStage.F π (flatLiftStage π K a k)

/-- Comparison maps `F^{a + 1 - k} ⟶ π_* K^{a + 1 - k}` of the recursive flat lift. -/
private noncomputable def flatLiftToK
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) (k : ℕ) :
    flatLiftX π K a k ⟶ (restrictionAlong π).obj (K.X (a + 1 - k)) :=
  FlatLiftStage.toK π (flatLiftStage π K a k)

/-- Outgoing differentials of the recursive flat lift, targeting the previous stage. -/
private noncomputable def flatLiftDOut
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) (k : ℕ) :
    flatLiftX π K a k ⟶ FlatLiftStage.Fpred π (flatLiftStage π K a k) :=
  FlatLiftStage.dOut π (flatLiftStage π K a k)

/-- The `ℕ`-offset of cohomological degree `n` relative to the bound `a`. -/
private def flatLiftOffset (a n : ℤ) : ℕ :=
  Int.toNat (a + 1 - n)

/-- Term of the recursive flat lift in cohomological degree `n`. -/
private noncomputable def flatLiftTerm
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  flatLiftX π K a (flatLiftOffset a n)

/-- Commuting `a + 1 - (n + 1)` into the `1 + a - (1 + n)` association. -/
private def int_add_one_sub_add_one (a n : ℤ) : a + 1 - (n + 1) = 1 + a - (1 + n) :=
  (congrArg (fun z : ℤ ↦ z - (n + 1)) (add_comm a 1)).trans
    (congrArg (fun z : ℤ ↦ 1 + a - z) (add_comm n 1))

/-- The offset of degree `n + 1` is the predecessor of the offset of degree `n` when `n ≤ a`. -/
private def flatLiftOffset_succ (a n : ℤ) (hn : n ≤ a) :
    (flatLiftOffset a n).pred = flatLiftOffset a (n + 1) :=
  Nat.cast_injective (R := ℤ) <|
    (congrArg (fun m : ℕ ↦ (m : ℤ))
        (Nat.pred_eq_sub_one (n := (a + 1 - n).toNat))).trans <|
      (Int.toNat_pred_coe_of_pos (sub_pos.mpr (Int.lt_add_one_iff.mpr hn))).trans <|
        (sub_sub (a + 1) n 1).trans <|
          (int_add_one_sub_add_one a n).trans <|
            (Int.toNat_of_nonneg
                (sub_nonneg.mpr (add_le_add_right hn (1 : ℤ)))).symm.trans <|
              congrArg (fun z : ℤ ↦ (z.toNat : ℤ)) (int_add_one_sub_add_one a n).symm

/-- Unfolding of the successor stage of the recursive flat lift. -/
private def flatLiftStage_succ_eq
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) (k : ℕ) :
    flatLiftStage π K a (k + 1) = FlatLiftStage.succ π (flatLiftStage π K a k) :=
  Nat.rec_add_one (C := fun n ↦ FlatLiftStage π K a n)
    (FlatLiftStage.zero π K a) (fun _ prev ↦ FlatLiftStage.succ π prev) k

/-- The previous-stage field at a positive offset is the lifted term in the next cohomological degree. -/
private def flatLift_Fpred_term
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) (hn : n ≤ a) :
    FlatLiftStage.Fpred π (flatLiftStage π K a (flatLiftOffset a n)) =
      flatLiftTerm π K a (n + 1) :=
  match hoff : flatLiftOffset a n with
  | 0 =>
    (not_le.mpr (Int.lt_add_one_iff.mpr hn)
      (sub_nonpos.mp (Int.toNat_eq_zero.mp hoff))).elim
  | k + 1 =>
    (congrArg (fun s : FlatLiftStage π K a (k + 1) ↦ FlatLiftStage.Fpred π s)
        (flatLiftStage_succ_eq π K a k)).trans <|
      (rfl : FlatLiftStage.Fpred π (FlatLiftStage.succ π (flatLiftStage π K a k)) =
          FlatLiftStage.F π (flatLiftStage π K a k)).trans
        (congrArg (flatLiftX π K a)
          ((Eq.symm (Nat.pred_succ k)).trans
            ((congrArg Nat.pred hoff).symm.trans (flatLiftOffset_succ a n hn))))

/-- `𝒪`-linear differential of the recursive flat lift in degree `n`. -/
private noncomputable def flatLiftD
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) :
    flatLiftTerm π K a n ⟶ flatLiftTerm π K a (n + 1) :=
  if hn : n ≤ a then
    flatLiftDOut π K a (flatLiftOffset a n) ≫
      eqToHom (flatLift_Fpred_term π K a n hn)
  else
    0

/-- Scalar extension of a term of the recursive flat lift. -/
private noncomputable def extendLiftTerm
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀ :=
  (ChangeOfRings.extendScalars (ringSheafMap π)).obj (flatLiftTerm π K a n)

/-- Scalar extension of a differential of the recursive flat lift. -/
private noncomputable def extendLiftD
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a i j : ℤ) :
    extendLiftTerm π K a i ⟶ extendLiftTerm π K a j :=
  if hij : i + 1 = j then
    (ChangeOfRings.extendScalars (ringSheafMap π)).map (flatLiftD π K a i) ≫
      eqToHom (congrArg (extendLiftTerm π K a) hij)
  else
    0

/-- After extension of scalars, consecutive differentials of the recursive flat lift square to zero. -/
private theorem extendLift_d_comp_d
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a i j k : ℤ) :
    extendLiftD π K a i j ≫ extendLiftD π K a j k = 0 := sorry

/-- The extended successive family `F₀^• = F^• ⊗_𝒪 𝒪₀` is a cochain complex. -/
private noncomputable def extendLiftComplex
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ where
  X n := extendLiftTerm π K a n
  d := extendLiftD π K a
  shape _ _ hij := dif_neg hij
  d_comp_d' i j k _ _ := extendLift_d_comp_d π K a i j k

/-- Adjunct of the stage comparison, as an `𝒪₀`-linear map `F₀^n ⟶ K^n`. -/
private noncomputable def extendLiftToK
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) :
    extendLiftTerm π K a n ⟶ K.X n :=
  if hn : n ≤ a + 1 then
    (ChangeOfRings.extendRestrictHomEquiv (ringSheafMap π)
        (flatLiftTerm π K a n) (K.X n)).symm
      (flatLiftToK π K a (flatLiftOffset a n) ≫
        eqToHom (congrArg ((restrictionAlong π).obj ∘ K.X)
          (int_offset_to_degree a n hn)))
  else
    0

/-- The comparison `F₀^• ⟶ K^•` commutes with differentials. -/
private theorem extendLiftComparison_comm
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a i j : ℤ) :
    extendLiftToK π K a i ≫ K.d i j =
      extendLiftD π K a i j ≫ extendLiftToK π K a j := sorry

/-- The chain map `F₀^• ⟶ K^•` of the recursive flat lift. -/
private noncomputable def extendLiftComparison
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) :
    extendLiftComplex π K a ⟶ K where
  f n := extendLiftToK π K a n
  comm' i j _ := extendLiftComparison_comm π K a i j

/-- The comparison `F₀^• ⟶ K^•` is a quasi-isomorphism when `K` is strictly bounded above by `a`. -/
private theorem extendLiftComparison_quasiIso
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    QuasiIso (extendLiftComparison π K a) := sorry

/-- `Q.map` of the recursive flat lift comparison is an isomorphism when `K` is strictly bounded above by `a`. -/
private instance instIsIso_Q_extendLiftComparison
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    IsIso (DerivedCategory.Q.map (extendLiftComparison π K a)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso
      (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)
      (extendLiftComparison π K a)).2
    (extendLiftComparison_quasiIso π K a)

/-- Inverse of `Q.map` of the recursive flat lift comparison, when `K` is strictly bounded above by `a`. -/
private noncomputable def extendLiftComparisonDerivedInv
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (extendLiftComplex π K a) :=
  (asIso (DerivedCategory.Q.map (extendLiftComparison π K a))).inv

/-- Termwise tensor of a cochain complex with the descended kernel ideal. -/
private noncomputable abbrev tensorKernelComplex
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ) :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ :=
  HomologicalComplex.tensorObj K (kernelIdeal0SingleComplex π h_sq)

/-- Restriction of scalars of the square-zero kernel module recovers the kernel ideal sheaf. -/
private noncomputable def restrictKernelIdeal0Iso :
    (restrictionAlong π).obj (kernelIdeal0 π h_sq) ≅ KernelIdeal.sheaf π :=
  h_sq.targetModuleRestrictIso inferInstance

/-- The action of the kernel ideal on an `𝒪`-module, via inclusion into the structure sheaf
and the left unitor. -/
private noncomputable def kernelIdealAct
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    moduleTensor (KernelIdeal.sheaf π) M ⟶ M :=
  (KernelIdeal.ι π ▷ M) ≫ (unitIsoTensorUnit.hom ▷ M) ≫ (λ_ M).hom

/-- Tensoring the kernel-ideal inclusion with `M` followed by the left unitor lands in the
kernel of the extension-restriction unit. -/
private theorem tensorKernelIdeal_comp_unit
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    kernelIdealAct π M ≫ extendRestrictUnit π M = 0 := sorry

/-- The map `ℐ ⊗ F ⟶ ker(unit)` induced by the kernel-ideal inclusion. -/
private noncomputable def tensorKernelIdealToUnitKernel
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    moduleTensor (KernelIdeal.sheaf π) M ⟶ kernel (extendRestrictUnit π M) :=
  kernel.lift (extendRestrictUnit π M) (kernelIdealAct π M)
    (tensorKernelIdeal_comp_unit π M)

/-- The comparison `ℐ ⊗ F ⟶ ker(unit)` is an isomorphism on the terms of the recursive flat lift. -/
private theorem isIso_tensorKernelIdealToUnitKernel_lift
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) :
    IsIso (tensorKernelIdealToUnitKernel π (flatLiftTerm π K a n)) := sorry

/-- The ideal tensor comparison is invertible on each recursively lifted term. -/
private instance instIsIso_tensorKernelIdealToUnitKernel_lift
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a n : ℤ) :
    IsIso (tensorKernelIdealToUnitKernel π (flatLiftTerm π K a n)) :=
  isIso_tensorKernelIdealToUnitKernel_lift π K a n

/-- Lifted `d ∘ d` composed with the extension-restriction unit vanishes, since `F₀` is a complex. -/
private theorem flatLift_dCompD_comp_unit
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a i : ℤ) :
    flatLiftD π K a i ≫ flatLiftD π K a (i + 1) ≫
      eqToHom (congrArg (flatLiftTerm π K a) (int_succ_succ i)) ≫
      extendRestrictUnit π (flatLiftTerm π K a (i + 2)) = 0 := sorry

/-- Comparison `restriction(ℐ₀) ⊗ M ⟶ restriction(ℐ₀ ⊗ extend M)`. -/
private noncomputable def restrictTensorCompare
    (M : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    moduleTensor ((restrictionAlong π).obj (kernelIdeal0 π h_sq)) M ⟶
      (restrictionAlong π).obj
        (moduleTensor (kernelIdeal0 π h_sq)
          ((ChangeOfRings.extendScalars (ringSheafMap π)).obj M)) :=
  ((restrictionAlong π).obj (kernelIdeal0 π h_sq) ◁ extendRestrictUnit π M) ≫
    Restriction.tensorComparison π (kernelIdeal0 π h_sq)
      ((ChangeOfRings.extendScalars (ringSheafMap π)).obj M)

/-- The cochain-level component of `ω` on the extended recursive flat lift, as an `𝒪₀`-linear map
into the termwise tensor with `ℐ`. -/
private noncomputable def canonicalClassComponent
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a i : ℤ) :
    extendLiftTerm π K a i ⟶
      moduleTensor (extendLiftTerm π K a (i + 2)) (kernelIdeal0 π h_sq) :=
  (ChangeOfRings.extendRestrictHomEquiv (ringSheafMap π)
      (flatLiftTerm π K a i)
      (moduleTensor (kernelIdeal0 π h_sq) (extendLiftTerm π K a (i + 2)))).symm
    (kernel.lift (extendRestrictUnit π (flatLiftTerm π K a (i + 2)))
        (flatLiftD π K a i ≫ flatLiftD π K a (i + 1) ≫
          eqToHom (congrArg (flatLiftTerm π K a) (int_succ_succ i)))
        (flatLift_dCompD_comp_unit π K a i) ≫
      (asIso (tensorKernelIdealToUnitKernel π (flatLiftTerm π K a (i + 2)))).inv ≫
      ((restrictKernelIdeal0Iso π h_sq).inv ▷ flatLiftTerm π K a (i + 2)) ≫
      restrictTensorCompare π h_sq (flatLiftTerm π K a (i + 2))) ≫
    (β_ (kernelIdeal0 π h_sq) (extendLiftTerm π K a (i + 2))).hom

/-- Commutation of `canonicalClassComponent` with differentials. -/
private theorem canonicalClass_ofLift_comm
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a i j : ℤ) :
    canonicalClassComponent π h_sq K a i ≫
        ((extendLiftTerm π K a (i + 2) ◁
            (HomologicalComplex.singleObjXSelf (up ℤ) (0 : ℤ)
              (kernelIdeal0 π h_sq)).inv) ≫
        HomologicalComplex.ιTensorObj (extendLiftComplex π K a)
          (kernelIdeal0SingleComplex π h_sq) (i + 2) 0 (i + 2) (add_zero (i + 2))) ≫
        ((tensorKernelComplex π h_sq (extendLiftComplex π K a))⟦(2 : ℤ)⟧).d i j =
      (extendLiftComplex π K a).d i j ≫
        canonicalClassComponent π h_sq K a j ≫
          ((extendLiftTerm π K a (j + 2) ◁
              (HomologicalComplex.singleObjXSelf (up ℤ) (0 : ℤ)
                (kernelIdeal0 π h_sq)).inv) ≫
          HomologicalComplex.ιTensorObj (extendLiftComplex π K a)
            (kernelIdeal0SingleComplex π h_sq) (j + 2) 0 (j + 2) (add_zero (j + 2))) := sorry

/-- The cochain map `F₀^• ⟶ (F₀^• ⊗ ℐ[0])⟦2⟧` presenting `ω` on the recursive flat lift. -/
private noncomputable def canonicalClass_ofLift
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) :
    extendLiftComplex π K a ⟶
      (tensorKernelComplex π h_sq (extendLiftComplex π K a))⟦(2 : ℤ)⟧ where
  f i :=
    canonicalClassComponent π h_sq K a i ≫
      ((extendLiftTerm π K a (i + 2) ◁
          (HomologicalComplex.singleObjXSelf (up ℤ) (0 : ℤ)
            (kernelIdeal0 π h_sq)).inv) ≫
      HomologicalComplex.ιTensorObj (extendLiftComplex π K a)
        (kernelIdeal0SingleComplex π h_sq) (i + 2) 0 (i + 2) (add_zero (i + 2)))
  comm' i j _ := canonicalClass_ofLift_comm π h_sq K a i j




/-- The two-variable derived tensor is compatible with fixed-right derivation at `ℐ[0]`. -/
instance instCompatible_kernelIdeal0Single :
    DerivedTensor.Bifunctor.Right.Compatible (kernelIdeal0Single π h_sq) := sorry

/-- The derived-tensor counit against `ℐ[0]` is invertible on the extended recursive flat lift. -/
private theorem isIso_counitAppOfQ_extendLift
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ (extendLiftComplex π K a)
      (kernelIdeal0SingleComplex π h_sq)) := sorry

/-- The derived tensor counit is invertible on the scalar-extended flat lift. -/
private instance instIsIso_counitAppOfQ_extendLift
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ (extendLiftComplex π K a)
      (kernelIdeal0SingleComplex π h_sq)) :=
  isIso_counitAppOfQ_extendLift π h_sq K a

/-- Comparison from the total tensor with `ℐ[0]` to the fixed-right derived tensor against
`ℐ[0]`, on the extended recursive flat lift. -/
private noncomputable def termwiseToDerivedTensor
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀) ℤ)
    (a : ℤ) :
    DerivedCategory.Q.obj (tensorKernelComplex π h_sq (extendLiftComplex π K a)) ⟶
      DerivedCategory.Q.obj (extendLiftComplex π K a) ⊗ᴸ kernelIdeal0Single π h_sq :=
  inv (DerivedTensor.Bifunctor.counitAppOfQ (extendLiftComplex π K a)
      (kernelIdeal0SingleComplex π h_sq)) ≫
    (DerivedTensor.Bifunctor.Right.isoApp (kernelIdeal0Single π h_sq)
      (DerivedCategory.Q.obj (extendLiftComplex π K a))).inv


/-- `Q.map` of the truncation comparison of a bounded-above representative is an isomorphism. -/
private instance instIsIso_Q_ιTruncLE
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    IsIso (DerivedCategory.Q.map
      ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK))) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso
      (ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)
      ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK))).2
    ((CochainComplex.quasiIso_ιTruncLE_iff _ _).2 inferInstance)

/-- Inverse of `Q.map` of the truncation comparison of a bounded-above representative. -/
private noncomputable def ιTruncLEDerivedInv
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K₀) ⟶
      DerivedCategory.Q.obj (boundedRepresentative K₀ hK) :=
  (asIso (DerivedCategory.Q.map
    ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK)))).inv

/-- The canonical morphism `ω(K₀) : K₀ ⟶ (K₀ ⊗ᴸ ℐ[0])⟦2⟧` in `D(𝒪₀)`. -/
noncomputable def canonicalClass
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    K₀ ⟶ tensorKernelShift π h_sq K₀ :=
  let a := isBoundedAboveBound K₀ hK
  let K := boundedRepresentative K₀ hK
  let P := extendLiftComplex π K a
  (DerivedCategory.Q.objObjPreimageIso K₀).inv ≫
    ιTruncLEDerivedInv K₀ hK ≫
    extendLiftComparisonDerivedInv π K a ≫
    DerivedCategory.Q.map (canonicalClass_ofLift π h_sq K a) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        (tensorKernelComplex π h_sq P) ≫
      ((shiftFunctor _ (2 : ℤ)).map (termwiseToDerivedTensor π h_sq K a)) ≫
      ((shiftFunctor _ (2 : ℤ)).map
        ((DerivedTensor.Right.functor (kernelIdeal0Single π h_sq)).map
          (DerivedCategory.Q.map (extendLiftComparison π K a) ≫
            DerivedCategory.Q.map
              ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK)) ≫
            (DerivedCategory.Q.objObjPreimageIso K₀).hom)))

/-- `canonicalClass` is `Q.map` of the cochain-level factorization of lifted `d ∘ d` on the
recursive flat lift of a bounded-above representative, transported to `K₀`. -/
private theorem canonicalClass_spec
    (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀)
    (hK : K₀.IsBoundedAbove) :
    canonicalClass π h_sq K₀ hK =
      (let a := isBoundedAboveBound K₀ hK
        let K := boundedRepresentative K₀ hK
        let P := extendLiftComplex π K a
        (DerivedCategory.Q.objObjPreimageIso K₀).inv ≫
          ιTruncLEDerivedInv K₀ hK ≫
          extendLiftComparisonDerivedInv π K a ≫
          DerivedCategory.Q.map (canonicalClass_ofLift π h_sq K a) ≫
            (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
              (tensorKernelComplex π h_sq P) ≫
            ((shiftFunctor _ (2 : ℤ)).map (termwiseToDerivedTensor π h_sq K a)) ≫
            ((shiftFunctor _ (2 : ℤ)).map
              ((DerivedTensor.Right.functor (kernelIdeal0Single π h_sq)).map
                (DerivedCategory.Q.map (extendLiftComparison π K a) ≫
                  DerivedCategory.Q.map
                    ((DerivedCategory.Q.objPreimage K₀).ιTruncLE
                      (isBoundedAboveBound K₀ hK)) ≫
                  (DerivedCategory.Q.objObjPreimageIso K₀).hom)))) := rfl

/-- The canonical square-zero obstruction commutes with every morphism between
cohomologically bounded-above derived modules. -/
theorem canonicalClass_natural
    {K₀ L₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀}
    (hK : K₀.IsBoundedAbove) (hL : L₀.IsBoundedAbove) (α : K₀ ⟶ L₀) :
    canonicalClass π h_sq K₀ hK ≫ tensorKernelShiftMap π h_sq α =
      α ≫ canonicalClass π h_sq L₀ hL := sorry

end

end RingedSite.Hom.ModuleDerived
