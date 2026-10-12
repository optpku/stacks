/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor

/-!
# Canonical class of a bounded-above complex on a square-zero ringed site

Along a locally surjective square-zero map `π : 𝒪 ⟶ 𝒪₀` of ring sheaves with kernel ideal `ℐ`,
every `K₀` in `D⁻(𝒪₀)` has a canonical morphism `ω(K₀) : K₀ ⟶ (K₀ ⊗ᴸ ℐ[0])⟦2⟧` in `D(𝒪₀)`.
The map is obtained from the G = 0 case of tag 0DIT: a bounded-above representative is lifted
to a successive family of flat `𝒪`-modules assembled as coproducts of `j_! 𝒪_U` on local
sections, the failure `d ∘ d` is factored through `ℐ`, and the resulting chain map of the
extended complex is transported along the quasi-isomorphism and the K-flat identification.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open HomologicalComplex
open Opposite
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open SheafOfModules
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, `Q`, and `DerivedTensor.Right.functor` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): `moduleMonoidalCategory` is the tensor used by `unitIsoTensorUnit`, whiskering, and `λ_`; it must agree with module-level tensors on `ringedSiteModuleCategory`.
attribute [local instance] SheafOfModules.RingedSite.moduleMonoidalCategory
-- Local instance justification (defeq pin): `moduleSymmetricCategory` supplies the braiding `I ⊗ F ≅ F ⊗ I` used to place the kernel ideal on the right in the cochain components of `ω`.
attribute [local instance] SheafOfModules.RingedSite.moduleSymmetricCategory

/-- Successor cancellation `n - 1 + 1 = n` on cohomological degrees. -/
def int_pred_succ (n : ℤ) : n - 1 + 1 = n :=
  sub_add_cancel n 1

/-- Degree identity `n + 1 + 1 = n + 2`. -/
def int_succ_succ (n : ℤ) : n + 1 + 1 = n + 2 :=
  (add_assoc n 1 1).trans (congrArg (HAdd.hAdd n) one_add_one_eq_two)

/-- Offset conversion `a + 1 - (k + 1) = (a + 1 - k) - 1`. -/
def int_offset_succ (a : ℤ) (k : ℕ) : a + 1 - (k + 1 : ℕ) = (a + 1 - k) - 1 :=
  (congrArg (fun z : ℤ ↦ a + 1 - z) (Nat.cast_succ k)).trans
    (sub_add_eq_sub_sub (a + 1) (k : ℤ) 1)

/-- Recovering a cohomological degree from its `ℕ`-offset below `a + 1`. -/
def int_offset_to_degree (a n : ℤ) (hn : n ≤ a + 1) :
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
variable [HasCoproducts.{max u w} (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [HasZeroObject (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
variable [@DerivedTensor.Right.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Bifunctor.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _ _ _ _ _]
variable [(restrictionAlong π).LaxMonoidal]

/-- The kernel ideal of `π`, regarded as an `𝒪₀`-module via square-zero descent. -/
noncomputable abbrev kernelIdeal0 :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  KernelIdeal.IsSquareZero.targetModule h_sq inferInstance

/-- The degree-zero single of the descended kernel ideal in `D(𝒪₀)`. -/
noncomputable abbrev kernelIdeal0Single :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (0 : ℤ)).obj
    (kernelIdeal0 π h_sq)

/-- The cochain complex `ℐ[0]` associated to the descended kernel ideal. -/
noncomputable abbrev kernelIdeal0SingleComplex :
    CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ :=
  (HomologicalComplex.single
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) (up ℤ) (0 : ℤ)).obj
    (kernelIdeal0 π h_sq)

/-- The shifted derived tensor `(K₀ ⊗ᴸ ℐ[0])⟦2⟧`. -/
noncomputable abbrev tensorKernelShift
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) :
    ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  (K₀ ⊗ᴸ kernelIdeal0Single π h_sq)⟦(2 : ℤ)⟧

/-- The map `(α ⊗ᴸ id_{ℐ[0]})⟦2⟧` induced by a morphism of derived `𝒪₀`-modules. -/
noncomputable def tensorKernelShiftMap
    {K₀ L₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (α : K₀ ⟶ L₀) :
    tensorKernelShift π h_sq K₀ ⟶ tensorKernelShift π h_sq L₀ :=
  (shiftFunctor _ (2 : ℤ)).map
    ((DerivedTensor.Right.functor (kernelIdeal0Single π h_sq)).map α)

/-- A chosen integer witnessing that a derived object is cohomologically bounded above. -/
def isBoundedAboveBound
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) : ℤ :=
  Classical.choose hK

/-- The chosen bound of `isBoundedAboveBound` witnesses `IsLE`. -/
instance instIsLE_isBoundedAboveBound
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    K₀.IsLE (isBoundedAboveBound K₀ hK) :=
  Classical.choose_spec hK

/-- A chosen preimage of a cohomologically bounded-above object remains bounded above. -/
instance instObjPreimage_isLE
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) {n : ℤ}
    [K₀.IsLE n] :
    (DerivedCategory.Q.objPreimage K₀).IsLE n :=
  (DerivedCategory.isLE_Q_obj_iff (DerivedCategory.Q.objPreimage K₀) n).mp
    (DerivedCategory.TStructure.t.isLE_of_iso
      (DerivedCategory.Q.objObjPreimageIso K₀).symm n)

/-- A strictly bounded-above cochain representative of a derived object of `D⁻(𝒪₀)`. -/
noncomputable def boundedRepresentative
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ :=
  (DerivedCategory.Q.objPreimage K₀).truncLE (isBoundedAboveBound K₀ hK)

/-- The chosen bounded-above representative is strictly supported in degrees at most the bound. -/
instance instBoundedRepresentative_isStrictlyLE
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    (boundedRepresentative K₀ hK).IsStrictlyLE (isBoundedAboveBound K₀ hK) :=
  inferInstanceAs
    (((DerivedCategory.Q.objPreimage K₀).truncLE (isBoundedAboveBound K₀ hK)).IsStrictlyLE
      (isBoundedAboveBound K₀ hK))

/-- Pairs `(U, s)` of a site object in universe `w` and a local section of an `𝒪`-module. -/
def localSectionIndex
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :=
  Σ U : C, (M.val.obj (op U) : Type w)

/-- The localized structure module `j_{U!} 𝒪_U`. -/
noncomputable def structureSummand (U : C) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  SheafOfModules.Localization.structureModule (ringSheaf J 𝒪) U

/-- Coproduct of `j_! 𝒪_U` indexed by all local sections of `M`. -/
noncomputable def sectionCoproduct
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  ∐ fun i : localSectionIndex M ↦ structureSummand i.1

/-- The summand map `j_{U!} 𝒪_U ⟶ M` sending the universal section to `s`. -/
noncomputable def structureSummandHom
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (i : localSectionIndex M) :
    structureSummand i.1 ⟶ M :=
  (SheafOfModules.Localization.structureModuleHomEquiv (ringSheaf J 𝒪) i.1 M).symm i.2

/-- Evaluation of the local-section coproduct on `M`. -/
noncomputable def sectionCoproductHom
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    sectionCoproduct M ⟶ M :=
  Sigma.desc (structureSummandHom M)

/-- The coproduct evaluation recovers the tautological section maps on summands. -/
theorem sectionCoproductHom_ι
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (i : localSectionIndex M) :
    Sigma.ι (fun j : localSectionIndex M ↦ structureSummand j.1) i ≫
      sectionCoproductHom M =
      structureSummandHom M i := sorry

/-- The adjunction unit of extension/restriction along `π`. -/
noncomputable abbrev extendRestrictUnit
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    M ⟶ (restrictionAlong π).obj
      ((ChangeOfRings.extendScalars (ringSheafMap π)).obj M) :=
  (ChangeOfRings.extendRestrictAdjunction (ringSheafMap π)).unit.app M

/-- Restriction of a successive differential of `K` to an `𝒪`-module morphism. -/
noncomputable def restrictedDiff
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ) :
    (restrictionAlong π).obj (K.X (e - 1)) ⟶ (restrictionAlong π).obj (K.X e) :=
  (restrictionAlong π).map
    (K.d (e - 1) (e - 1 + 1) ≫ eqToHom (congrArg K.X (int_pred_succ e)))

/-- Cycles in a lifted term that map to boundaries in `K`, as an `𝒪`-module pullback. -/
noncomputable def cycleBoundaryPullback
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  pullback (kernel.ι (dOut ≫ extendRestrictUnit π Fprev) ≫ toK) (restrictedDiff π K e)

/-- Kernel of `π_* (K^{e - 1} ⟶ K^e)`, generating the C summand of tag 0DIT. -/
noncomputable def homologyKernelRestrict
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  kernel (restrictedDiff π K e)

/-- The B-summand of the next lifted term is the local-section coproduct of the cycle pullback. -/
noncomputable def liftSummandB
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  sectionCoproduct (cycleBoundaryPullback π K e dOut toK)

/-- The C-summand of the next lifted term is the local-section coproduct of homology cycles. -/
noncomputable def liftSummandC
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  sectionCoproduct (homologyKernelRestrict π K e)

/-- The B-summand map into the previous lifted term. -/
noncomputable def liftSummandBToPrev
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSummandB π K e dOut toK ⟶ F :=
  sectionCoproductHom (cycleBoundaryPullback π K e dOut toK) ≫
    pullback.fst (kernel.ι (dOut ≫ extendRestrictUnit π Fprev) ≫ toK)
      (restrictedDiff π K e) ≫
    kernel.ι (dOut ≫ extendRestrictUnit π Fprev)

/-- The B-summand comparison into `π_* K^{e - 1}`. -/
noncomputable def liftSummandBToK
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSummandB π K e dOut toK ⟶ (restrictionAlong π).obj (K.X (e - 1)) :=
  sectionCoproductHom (cycleBoundaryPullback π K e dOut toK) ≫
    pullback.snd (kernel.ι (dOut ≫ extendRestrictUnit π Fprev) ≫ toK)
      (restrictedDiff π K e)

/-- The C-summand comparison into `π_* K^{e - 1}`. -/
noncomputable def liftSummandCToK
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ) :
    liftSummandC π K e ⟶ (restrictionAlong π).obj (K.X (e - 1)) :=
  sectionCoproductHom (homologyKernelRestrict π K e) ≫ kernel.ι (restrictedDiff π K e)

/-- Next lifted term `B ⊞ C` in the G = 0 case of tag 0DIT. -/
noncomputable def liftSuccX
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  liftSummandB π K e dOut toK ⊞ liftSummandC π K e

/-- Outgoing differential of the successor term onto the previous lifted module. -/
noncomputable def liftSuccDOut
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSuccX π K e dOut toK ⟶ F :=
  biprod.desc (liftSummandBToPrev π K e dOut toK) 0

/-- Comparison of the successor term into `π_* K^{e - 1}`. -/
noncomputable def liftSuccToK
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (e : ℤ)
    {F Fprev : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (dOut : F ⟶ Fprev)
    (toK : F ⟶ (restrictionAlong π).obj (K.X e)) :
    liftSuccX π K e dOut toK ⟶ (restrictionAlong π).obj (K.X (e - 1)) :=
  biprod.desc (liftSummandBToK π K e dOut toK) (liftSummandCToK π K e)

/-- One degree of the G = 0 lift: a flat `𝒪`-module assembled from `j_! 𝒪_U`, its comparison
to `K`, and the outgoing differential onto the previous stage. -/
structure FlatLiftStage
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) (k : ℕ) where
  /-- The `𝒪`-module `F^{a + 1 - k}`. -/
  F : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)
  /-- The previous stage module, or the zero module at `k = 0`. -/
  Fpred : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)
  /-- Comparison `F^{a + 1 - k} ⟶ π_* K^{a + 1 - k}`. -/
  toK : F ⟶ (restrictionAlong π).obj (K.X (a + 1 - k))
  /-- Outgoing differential `F^{a + 1 - k} ⟶ F^{a + 2 - k}`. -/
  dOut : F ⟶ Fpred

/-- The vanishing stage in degrees `> a`. -/
noncomputable def flatLiftStageZero
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) : FlatLiftStage π K a 0 where
  F := 0
  Fpred := 0
  toK := 0
  dOut := 0

/-- One inductive step of the G = 0 lift, taking `F^{e - 1} = B ⊞ C`. -/
noncomputable def flatLiftStageSucc
    {K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ}
    {a : ℤ} {k : ℕ} (prev : FlatLiftStage π K a k) :
    FlatLiftStage π K a (k + 1) where
  F := liftSuccX π K (a + 1 - k) prev.dOut prev.toK
  Fpred := prev.F
  toK := liftSuccToK π K (a + 1 - k) prev.dOut prev.toK ≫
    eqToHom (congrArg ((restrictionAlong π).obj ∘ K.X) (int_offset_succ a k).symm)
  dOut := liftSuccDOut π K (a + 1 - k) prev.dOut prev.toK

/-- Termwise G = 0 lift data in offset `k` below the bound. -/
noncomputable def flatLiftStage
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) (k : ℕ) : FlatLiftStage π K a k :=
  Nat.rec (motive := fun n ↦ FlatLiftStage π K a n)
    (flatLiftStageZero π K a) (fun _ prev ↦ flatLiftStageSucc π prev) k

/-- The G = 0 successive lift of a bounded-above complex, as `𝒪`-modules `F^{a + 1 - k}`. -/
noncomputable def flatLiftX
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) (k : ℕ) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  (flatLiftStage π K a k).F

/-- Comparison maps `F^{a + 1 - k} ⟶ π_* K^{a + 1 - k}` of the G = 0 lift. -/
noncomputable def flatLiftToK
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) (k : ℕ) :
    flatLiftX π K a k ⟶ (restrictionAlong π).obj (K.X (a + 1 - k)) :=
  (flatLiftStage π K a k).toK

/-- Outgoing differentials of the G = 0 lift, targeting the previous stage. -/
noncomputable def flatLiftDOut
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) (k : ℕ) :
    flatLiftX π K a k ⟶ (flatLiftStage π K a k).Fpred :=
  (flatLiftStage π K a k).dOut

/-- The `ℕ`-offset of cohomological degree `n` relative to the bound `a`. -/
def flatLiftOffset (a n : ℤ) : ℕ :=
  Int.toNat (a + 1 - n)

/-- Term of the G = 0 lift in cohomological degree `n`. -/
noncomputable def flatLiftTerm
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a n : ℤ) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪) :=
  flatLiftX π K a (flatLiftOffset a n)

/-- Commuting `a + 1 - (n + 1)` into the `1 + a - (1 + n)` association. -/
def int_add_one_sub_add_one (a n : ℤ) : a + 1 - (n + 1) = 1 + a - (1 + n) :=
  (congrArg (fun z : ℤ ↦ z - (n + 1)) (add_comm a 1)).trans
    (congrArg (fun z : ℤ ↦ 1 + a - z) (add_comm n 1))

/-- The offset of degree `n + 1` is the predecessor of the offset of degree `n` when `n ≤ a`. -/
def flatLiftOffset_succ (a n : ℤ) (hn : n ≤ a) :
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

/-- Unfolding of the successor stage of the G = 0 lift. -/
def flatLiftStage_succ_eq
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) (k : ℕ) :
    flatLiftStage π K a (k + 1) = flatLiftStageSucc π (flatLiftStage π K a k) :=
  Nat.rec_add_one (C := fun n ↦ FlatLiftStage π K a n)
    (flatLiftStageZero π K a) (fun _ prev ↦ flatLiftStageSucc π prev) k

/-- The previous-stage field at a positive offset is the lifted term in the next cohomological degree. -/
def flatLift_Fpred_term
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a n : ℤ) (hn : n ≤ a) :
    (flatLiftStage π K a (flatLiftOffset a n)).Fpred = flatLiftTerm π K a (n + 1) :=
  match hoff : flatLiftOffset a n with
  | 0 =>
    (not_le.mpr (Int.lt_add_one_iff.mpr hn)
      (sub_nonpos.mp (Int.toNat_eq_zero.mp hoff))).elim
  | k + 1 =>
    (congrArg (fun s : FlatLiftStage π K a (k + 1) ↦ s.Fpred)
        (flatLiftStage_succ_eq π K a k)).trans <|
      (rfl : (flatLiftStageSucc π (flatLiftStage π K a k)).Fpred =
          (flatLiftStage π K a k).F).trans
        (congrArg (flatLiftX π K a)
          ((Eq.symm (Nat.pred_succ k)).trans
            ((congrArg Nat.pred hoff).symm.trans (flatLiftOffset_succ a n hn))))

/-- `𝒪`-linear differential of the G = 0 lift in degree `n`. -/
noncomputable def flatLiftD
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a n : ℤ) :
    flatLiftTerm π K a n ⟶ flatLiftTerm π K a (n + 1) :=
  if hn : n ≤ a then
    flatLiftDOut π K a (flatLiftOffset a n) ≫
      eqToHom (flatLift_Fpred_term π K a n hn)
  else
    0

/-- Scalar extension of a term of the G = 0 lift. -/
noncomputable def extendLiftTerm
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a n : ℤ) :
    ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀) :=
  (ChangeOfRings.extendScalars (ringSheafMap π)).obj (flatLiftTerm π K a n)

/-- Scalar extension of a differential of the G = 0 lift. -/
noncomputable def extendLiftD
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a i j : ℤ) :
    extendLiftTerm π K a i ⟶ extendLiftTerm π K a j :=
  if hij : i + 1 = j then
    (ChangeOfRings.extendScalars (ringSheafMap π)).map (flatLiftD π K a i) ≫
      eqToHom (congrArg (extendLiftTerm π K a) hij)
  else
    0

/-- After extension of scalars, consecutive differentials of the G = 0 lift square to zero. -/
theorem extendLift_d_comp_d
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a i j k : ℤ) :
    extendLiftD π K a i j ≫ extendLiftD π K a j k = 0 := sorry

/-- The extended successive family `F₀^• = F^• ⊗_𝒪 𝒪₀` is a cochain complex. -/
noncomputable def extendLiftComplex
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) :
    CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ where
  X n := extendLiftTerm π K a n
  d := extendLiftD π K a
  shape _ _ hij := dif_neg hij
  d_comp_d' i j k _ _ := extendLift_d_comp_d π K a i j k

/-- Adjunct of the stage comparison, as an `𝒪₀`-linear map `F₀^n ⟶ K^n`. -/
noncomputable def extendLiftToK
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
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
theorem extendLiftComparison_comm
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a i j : ℤ) :
    extendLiftToK π K a i ≫ K.d i j =
      extendLiftD π K a i j ≫ extendLiftToK π K a j := sorry

/-- The chain map `F₀^• ⟶ K^•` of the G = 0 lift. -/
noncomputable def extendLiftComparison
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) :
    extendLiftComplex π K a ⟶ K where
  f n := extendLiftToK π K a n
  comm' i j _ := extendLiftComparison_comm π K a i j

/-- The comparison `F₀^• ⟶ K^•` is a quasi-isomorphism when `K` is strictly bounded above by `a`. -/
theorem extendLiftComparison_quasiIso
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    QuasiIso (extendLiftComparison π K a) := sorry

/-- `Q.map` of the G = 0 lift comparison is an isomorphism when `K` is strictly bounded above by `a`. -/
instance instIsIso_Q_extendLiftComparison
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    IsIso (DerivedCategory.Q.map (extendLiftComparison π K a)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
      (extendLiftComparison π K a)).2
    (extendLiftComparison_quasiIso π K a)

/-- Inverse of `Q.map` of the G = 0 lift comparison, when `K` is strictly bounded above by `a`. -/
noncomputable def extendLiftComparisonDerivedInv
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) [K.IsStrictlyLE a] :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (extendLiftComplex π K a) :=
  (asIso (DerivedCategory.Q.map (extendLiftComparison π K a))).inv

/-- Termwise tensor of a cochain complex with the descended kernel ideal. -/
noncomputable abbrev tensorKernelComplex
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ) :
    CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ :=
  HomologicalComplex.tensorObj K (kernelIdeal0SingleComplex π h_sq)

/-- The underlying additive comparison from the restricted square-zero kernel module to the
kernel ideal sheaf. -/
noncomputable def restrictKernelIdeal0ToPresheaf :
    ((restrictionAlong π).obj (kernelIdeal0 π h_sq)).val.presheaf ⟶
      (KernelIdeal.sheaf π).val.presheaf :=
  (h_sq.targetModuleForgetIso inferInstance).hom.hom

/-- The inverse underlying additive comparison from the kernel ideal sheaf to the restricted
square-zero kernel module. -/
noncomputable def restrictKernelIdeal0InvToPresheaf :
    (KernelIdeal.sheaf π).val.presheaf ⟶
      ((restrictionAlong π).obj (kernelIdeal0 π h_sq)).val.presheaf :=
  (h_sq.targetModuleForgetIso inferInstance).inv.hom

/-- The underlying additive comparison `restrictKernelIdeal0ToPresheaf` is linear over `𝒪`. -/
theorem restrictKernelIdeal0ToPresheaf_smul (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪).obj.obj U)
    (m : ((restrictionAlong π).obj (kernelIdeal0 π h_sq)).val.obj U) :
    (restrictKernelIdeal0ToPresheaf π h_sq).app U (r • m) =
      r • (restrictKernelIdeal0ToPresheaf π h_sq).app U m := sorry

/-- The inverse underlying additive comparison is linear over `𝒪`. -/
theorem restrictKernelIdeal0InvToPresheaf_smul (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪).obj.obj U)
    (m : (KernelIdeal.sheaf π).val.obj U) :
    (restrictKernelIdeal0InvToPresheaf π h_sq).app U (r • m) =
      r • (restrictKernelIdeal0InvToPresheaf π h_sq).app U m := sorry

/-- Restriction of scalars of the square-zero kernel module recovers the kernel ideal sheaf. -/
noncomputable def restrictKernelIdeal0Iso :
    (restrictionAlong π).obj (kernelIdeal0 π h_sq) ≅ KernelIdeal.sheaf π where
  hom := ⟨PresheafOfModules.homMk
    (restrictKernelIdeal0ToPresheaf π h_sq) (restrictKernelIdeal0ToPresheaf_smul π h_sq)⟩
  inv := ⟨PresheafOfModules.homMk
    (restrictKernelIdeal0InvToPresheaf π h_sq) (restrictKernelIdeal0InvToPresheaf_smul π h_sq)⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The action of the kernel ideal on an `𝒪`-module, via inclusion into the structure sheaf
and the left unitor. -/
noncomputable def kernelIdealAct
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    moduleTensor (KernelIdeal.sheaf π) M ⟶ M :=
  (KernelIdeal.ι π ▷ M) ≫ (unitIsoTensorUnit.hom ▷ M) ≫ (λ_ M).hom

/-- Tensoring the kernel-ideal inclusion with `M` followed by the left unitor lands in the
kernel of the extension-restriction unit. -/
theorem tensorKernelIdeal_comp_unit
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    kernelIdealAct π M ≫ extendRestrictUnit π M = 0 := sorry

/-- The map `ℐ ⊗ F ⟶ ker(unit)` induced by the kernel-ideal inclusion. -/
noncomputable def tensorKernelIdealToUnitKernel
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    moduleTensor (KernelIdeal.sheaf π) M ⟶ kernel (extendRestrictUnit π M) :=
  kernel.lift (extendRestrictUnit π M) (kernelIdealAct π M)
    (tensorKernelIdeal_comp_unit π M)

/-- The comparison `ℐ ⊗ F ⟶ ker(unit)` is an isomorphism on the terms of the G = 0 lift. -/
theorem isIso_tensorKernelIdealToUnitKernel_lift
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a n : ℤ) :
    IsIso (tensorKernelIdealToUnitKernel π (flatLiftTerm π K a n)) := sorry

/-- Instance wrapper for `isIso_tensorKernelIdealToUnitKernel_lift`. -/
instance instIsIso_tensorKernelIdealToUnitKernel_lift
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a n : ℤ) :
    IsIso (tensorKernelIdealToUnitKernel π (flatLiftTerm π K a n)) :=
  isIso_tensorKernelIdealToUnitKernel_lift π K a n

/-- Lifted `d ∘ d` composed with the extension-restriction unit vanishes, since `F₀` is a complex. -/
theorem flatLift_dCompD_comp_unit
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a i : ℤ) :
    flatLiftD π K a i ≫ flatLiftD π K a (i + 1) ≫
      eqToHom (congrArg (flatLiftTerm π K a) (int_succ_succ i)) ≫
      extendRestrictUnit π (flatLiftTerm π K a (i + 2)) = 0 := sorry

/-- Comparison `restriction(ℐ₀) ⊗ M ⟶ restriction(ℐ₀ ⊗ extend M)`. -/
noncomputable def restrictTensorCompare
    (M : ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    moduleTensor ((restrictionAlong π).obj (kernelIdeal0 π h_sq)) M ⟶
      (restrictionAlong π).obj
        (moduleTensor (kernelIdeal0 π h_sq)
          ((ChangeOfRings.extendScalars (ringSheafMap π)).obj M)) :=
  ((restrictionAlong π).obj (kernelIdeal0 π h_sq) ◁ extendRestrictUnit π M) ≫
    Functor.LaxMonoidal.μ (restrictionAlong π) (kernelIdeal0 π h_sq)
      ((ChangeOfRings.extendScalars (ringSheafMap π)).obj M)

/-- The cochain-level component of `ω` on the extended G = 0 lift, as an `𝒪₀`-linear map
into the termwise tensor with `ℐ`. -/
noncomputable def canonicalClassComponent
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
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
theorem canonicalClass_ofLift_comm
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
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

/-- The cochain map `F₀^• ⟶ (F₀^• ⊗ ℐ[0])⟦2⟧` presenting `ω` on the G = 0 lift. -/
noncomputable def canonicalClass_ofLift
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
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

/-- Left-associated totalization coherence for complexes of `𝒪₀`-modules. -/
instance instHasGoodTensor₁₂Tensor₀
    (G₁ G₂ G₃ : GradedObject ℤ
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
  RingedSite.CochainComplex.IntGraded.hasGoodTensor₁₂Tensor 𝒪₀ G₁ G₂ G₃

/-- Right-associated totalization coherence for complexes of `𝒪₀`-modules. -/
instance instHasGoodTensorTensor₂₃₀
    (G₁ G₂ G₃ : GradedObject ℤ
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
  RingedSite.CochainComplex.IntGraded.hasGoodTensorTensor₂₃ 𝒪₀ G₁ G₂ G₃

/-- Fourfold totalization coherence for complexes of `𝒪₀`-modules. -/
instance instHasTensor₄ObjExt₀
    (G₁ G₂ G₃ G₄ : GradedObject ℤ
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
  RingedSite.CochainComplex.IntGraded.hasTensor₄ObjExt 𝒪₀ G₁ G₂ G₃ G₄

/-- The two-variable derived tensor is compatible with fixed-right derivation at `ℐ[0]`. -/
instance instCompatible_kernelIdeal0Single :
    DerivedTensor.Bifunctor.Right.Compatible (kernelIdeal0Single π h_sq) := sorry

/-- The derived-tensor counit against `ℐ[0]` is invertible on the extended G = 0 lift. -/
theorem isIso_counitAppOfQ_extendLift
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ (extendLiftComplex π K a)
      (kernelIdeal0SingleComplex π h_sq)) := sorry

/-- Instance wrapper for `isIso_counitAppOfQ_extendLift`. -/
instance instIsIso_counitAppOfQ_extendLift
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) :
    IsIso (DerivedTensor.Bifunctor.counitAppOfQ (extendLiftComplex π K a)
      (kernelIdeal0SingleComplex π h_sq)) :=
  isIso_counitAppOfQ_extendLift π h_sq K a

/-- Comparison from the total tensor with `ℐ[0]` to the fixed-right derived tensor against
`ℐ[0]`, on the extended G = 0 lift. -/
noncomputable def termwiseToDerivedTensor
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ)
    (a : ℤ) :
    DerivedCategory.Q.obj (tensorKernelComplex π h_sq (extendLiftComplex π K a)) ⟶
      DerivedCategory.Q.obj (extendLiftComplex π K a) ⊗ᴸ kernelIdeal0Single π h_sq :=
  inv (DerivedTensor.Bifunctor.counitAppOfQ (extendLiftComplex π K a)
      (kernelIdeal0SingleComplex π h_sq)) ≫
    (DerivedTensor.Bifunctor.Right.isoApp (kernelIdeal0Single π h_sq)
      (DerivedCategory.Q.obj (extendLiftComplex π K a))).inv

/-- The truncation comparison of a bounded-above representative is a quasi-isomorphism. -/
theorem ιTruncLE_quasiIso
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    QuasiIso ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK)) :=
  sorry

/-- `Q.map` of the truncation comparison of a bounded-above representative is an isomorphism. -/
instance instIsIso_Q_ιTruncLE
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    IsIso (DerivedCategory.Q.map
      ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK))) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
      ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK))).2
    (ιTruncLE_quasiIso K₀ hK)

/-- Inverse of `Q.map` of the truncation comparison of a bounded-above representative. -/
noncomputable def ιTruncLEDerivedInv
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K₀) ⟶
      DerivedCategory.Q.obj (boundedRepresentative K₀ hK) :=
  (asIso (DerivedCategory.Q.map
    ((DerivedCategory.Q.objPreimage K₀).ιTruncLE (isBoundedAboveBound K₀ hK)))).inv

/-- The canonical morphism `ω(K₀) : K₀ ⟶ (K₀ ⊗ᴸ ℐ[0])⟦2⟧` in `D(𝒪₀)`. -/
noncomputable def canonicalClass
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
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
G = 0 lift of a bounded-above representative, transported to `K₀`. -/
theorem canonicalClass_spec
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
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
                  (DerivedCategory.Q.objObjPreimageIso K₀).hom)))) := sorry

end

end RingedSite.Hom.ModuleDerived
