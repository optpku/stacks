/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Fiber
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Solution
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Ext
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Cotangent Ext² existence obstruction of a first-order thickening of ringed topoi

A first-order thickening `t`, a morphism `f` of ringed topoi, a module `G`, and a
map `c : f⁻¹J ⟶ G` determine a canonical cotangent Ext² class. It is the connecting
image of the tautological Ext¹ class along the transitivity triangle of `f` and `t`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.FirstOrderThickening (sameSiteToposHom)
open RingedSite.ToposHom
open scoped DerivedExt RingedSite.ToposHom SheafOfModules.RingedSite

namespace RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JD.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

-- Local instance justification (defeq pin): pin Q, singleFunctor, and Ext to the reducible standard derived category of the site-presented module category.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): pin ModuleDerived and site-presented Ext to the same standard derived-category localization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/-- Identity inverse image of `O_{B'}` recovers `O_{B'}` on the target site. -/
def thickeningSourceIso :
    ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB') ≅ OB' :=
  InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimageIso
    (((sameSiteToposHom t).toTopos.commRingInverseImageForgetRingIso.app OB') ≪≫
      (MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := JD)).app (ringSheaf JD OB'))

/-- Inverse image of `t` as a commutative ring-sheaf map on the source site of `f`. -/
def pulledThickening : f.toTopos.commRingInverseImage.obj OB' ⟶ f.toTopos.commRingInverseImage.obj OB :=
  f.toTopos.commRingInverseImage.map t

/-- Inverse image along `f` preserves first-order thickenings. -/
instance pulled_isFirstOrderThickening :
    IsFirstOrderThickening (pulledThickening t f) :=
  sorry

/-- Inverse image of `thickeningSourceIso.hom` along `f`. -/
def pulledSourceMap :
    f.toTopos.commRingInverseImage.obj ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB') ⟶
      f.toTopos.commRingInverseImage.obj OB' :=
  f.toTopos.commRingInverseImage.map (thickeningSourceIso t).hom

/-- After the identity inverse-image comparison, `pulledStructureMap f (sameSiteToposHom t)` is `pulledSourceMap ≫ pulledThickening`. -/
theorem pulledBaseMap_eq_composite :
    pulledStructureMap f (sameSiteToposHom t) =
      pulledSourceMap t f ≫ pulledThickening t f :=
  sorry

/-- Additive comparison of `f⁻¹J` with the kernel of `pulledThickening`. -/
def inverseImageIdeal_additiveCompare :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal (pulledThickening t f)) :=
  KernelIdeal.additiveLift (pulledThickening t f) (inverseImageIdeal_toUnit f t) sorry ≫
    ((pulled_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso inferInstance).inv

/-- Module comparison `f⁻¹J ⟶ Ker(pulled t)`. -/
def inverseImageIdealCompare :
    inverseImageIdeal f t ⟶
      SheafOfModules.RingedSite.FirstOrderThickening.ideal (pulledThickening t f) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{u}).map (inverseImageIdeal_additiveCompare t f))
      (fun _ _ _ ↦ sorry)

/-- The additive inclusion of `f⁻¹J` is killed by the inverse-image ring map of `t`. -/
theorem inverseImageIdeal_toUnit_comp_unitUnderlyingMap :
    inverseImageIdeal_toUnit f t ≫
      SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t) = 0 :=
  sorry

/-- The kernel-ideal inclusion of `pulledThickening`, after forgetting to the source ring, is
killed by the inverse-image ring map of `t`. -/
theorem pulled_ι_comp_unitUnderlyingMap :
    (((pulled_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
          inferInstance).hom ≫
        (SheafOfModules.toSheaf
            (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB'))).map
          (KernelIdeal.ι (pulledThickening t f))) ≫
      SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t) = 0 :=
  sorry

/-- Additive reverse comparison of `Ker(pulled t)` with the kernel of the inverse-image ring
map of `t`. -/
def inverseImageIdeal_additiveCompare_inv :
    (SheafOfModules.toSheaf (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal (pulledThickening t f)) ⟶
      kernel (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) :=
  kernel.lift (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t))
    (((pulled_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
        inferInstance).hom ≫
      (SheafOfModules.toSheaf
          (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB'))).map
        (KernelIdeal.ι (pulledThickening t f)))
    (pulled_ι_comp_unitUnderlyingMap t f)

/-- Canonical kernel lift of the additive inclusion of `f⁻¹J`. -/
def inverseImageIdeal_toKernel :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      kernel (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) :=
  kernel.lift (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t))
    (inverseImageIdeal_toUnit f t) (inverseImageIdeal_toUnit_comp_unitUnderlyingMap t f)

/-- The additive inclusion of `f⁻¹J` is a monomorphism. -/
instance inverseImageIdeal_toUnit_mono :
    Mono (inverseImageIdeal_toUnit f t) :=
  (bottomRow_shortExact f t).mono_f

/-- Kernel-comparison isomorphism of `f⁻¹J` with the kernel of the inverse-image ring map
of `t`. The inverse is the unique factorization of `kernel.ι` through the kernel inclusion
`inverseImageIdeal_toUnit`, not a sectionwise preimage. -/
def inverseImageIdeal_toKernelIso :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ≅
      kernel (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) :=
  (ShortComplex.ShortExact.fIsKernel (bottomRow_shortExact f t)).conePointUniqueUpToIso
    (limit.isLimit
      (parallelPair (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) 0))

/-- The forward map of `inverseImageIdeal_toKernelIso` is the canonical kernel lift. -/
theorem inverseImageIdeal_toKernelIso_hom :
    (inverseImageIdeal_toKernelIso t f).hom = inverseImageIdeal_toKernel t f :=
  sorry

/-- Reverse comparison of the kernel of the inverse-image ring map with `f⁻¹J`. -/
def inverseImageIdeal_ofKernel :
    kernel (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) ⟶
      (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) :=
  (inverseImageIdeal_toKernelIso t f).inv

/-- Module reverse comparison `Ker(pulled t) ⟶ f⁻¹J`. -/
def inverseImageIdealCompare_inv :
    SheafOfModules.RingedSite.FirstOrderThickening.ideal (pulledThickening t f) ⟶
      inverseImageIdeal f t where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{u}).map
        (inverseImageIdeal_additiveCompare_inv t f ≫ inverseImageIdeal_ofKernel t f))
      (fun _ _ _ ↦ sorry)

/-- Identification of `f⁻¹J` with the kernel module of `pulledThickening`. -/
def inverseImageIdealIso :
    inverseImageIdeal f t ≅
      SheafOfModules.RingedSite.FirstOrderThickening.ideal (pulledThickening t f) where
  hom := inverseImageIdealCompare t f
  inv := inverseImageIdealCompare_inv t f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction of scalars along `f.structureMap` agrees with restriction along
`commRingStructureMap f`. -/
def restrictScalarsCompare :
    (SheafOfModules.restrictScalars f.structureMap).obj G ≅
      (restrictionAlong (commRingStructureMap f)).obj G := by
  change (SheafOfModules.restrictScalars f.structureMap).obj G ≅
    (SheafOfModules.restrictScalars (ringSheafOfCommMap (commRingStructureMap f))).obj G
  rw [commRingStructureMap_forget]
  have h : f.toTopos.commRingInverseImageForgetRingIso.hom.app OB = 𝟙 _ := by
    simp [MorphismOfTopoiIn.commRingInverseImageForgetRingIso,
      InternalCommRing.toInternalForgetRingIso, InternalCommRing.fromInternalForgetRingIso,
      Functor.mapCommRingOfFiniteProductsForgetRingIso]
    repeat first | erw [Functor.map_id] | erw [Category.id_comp]
    erw [f.toTopos.internalRingInverseImage.map_id]
    erw [(InternalRing.fromInternal (J := JC)).map_id, Category.id_comp]
    rfl
  erw [h, Category.id_comp]
  exact Iso.refl _

/-- The coefficient map of the pulled same-site equation, as a map out of `Ker(pulled t)`. -/
def coeffSameSite :
    (pulled_isFirstOrderThickening t f).isSquareZero.targetModule
        (KernelIdeal.quotientComparison_isIso (pulledThickening t f)) ⟶
      (restrictionAlong (commRingStructureMap f)).obj G :=
  (inverseImageIdealIso t f).inv ≫ c ≫ (restrictScalarsCompare f G).hom

/-- Inverse image along `f` of the identity thickening of `t` remains first-order. -/
instance pulledBaseMap_isFirstOrderThickening :
    IsFirstOrderThickening (pulledStructureMap f (sameSiteToposHom t)) :=
  sorry

/-- Additive inclusion of `f⁻¹J` into the unit of the source of `pulledStructureMap f (sameSiteToposHom t)`. -/
private def inverseImageIdeal_toUnitBase :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf
          (ringSheaf JC
            (f.toTopos.commRingInverseImage.obj
              ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB')))).obj
        (SheafOfModules.unit
          (ringSheaf JC
            (f.toTopos.commRingInverseImage.obj
              ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB')))) :=
  inverseImageIdeal_toUnit f t ≫
    SheafOfModules.unitUnderlyingMap
      (ringSheafMap (f.toTopos.commRingInverseImage.map (thickeningSourceIso t).inv))

/-- The inclusion of `f⁻¹J` is killed by `pulledStructureMap f (sameSiteToposHom t)`. -/
private theorem inverseImageIdeal_toUnitBase_comp :
    inverseImageIdeal_toUnitBase t f ≫
      SheafOfModules.unitUnderlyingMap
        (ringSheafMap (pulledStructureMap f (sameSiteToposHom t))) = 0 :=
  sorry

/-- Additive comparison of `f⁻¹J` with the kernel of `pulledStructureMap f (sameSiteToposHom t)`. -/
private def inverseImageIdeal_additiveCompareBase :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf
          (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal
          (pulledStructureMap f (sameSiteToposHom t))) :=
  KernelIdeal.additiveLift (pulledStructureMap f (sameSiteToposHom t))
    (inverseImageIdeal_toUnitBase t f) (inverseImageIdeal_toUnitBase_comp t f) ≫
    ((pulledBaseMap_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
      inferInstance).inv

/-- Module comparison `f⁻¹J ⟶ Ker(pulledBaseMap)`. -/
private def inverseImageIdealCompareBase :
    inverseImageIdeal f t ⟶
      SheafOfModules.RingedSite.FirstOrderThickening.ideal
        (pulledStructureMap f (sameSiteToposHom t)) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{u}).map
        (inverseImageIdeal_additiveCompareBase t f))
      (fun _ _ _ ↦ sorry)

/-- The additive inclusion of `f⁻¹J` into the source of `pulledStructureMap f (sameSiteToposHom t)` is a monomorphism. -/
private instance inverseImageIdeal_toUnitBase_mono :
    Mono (inverseImageIdeal_toUnitBase t f) :=
  sorry

/-- The kernel-ideal inclusion of `pulledStructureMap f (sameSiteToposHom t)` vanishes on the cokernel of
`inverseImageIdeal_toUnitBase`. -/
private theorem inverseImageIdeal_ι_comp_toUnitBase_coker :
    ((SheafOfModules.toSheaf
        (ringSheaf JC
          (f.toTopos.commRingInverseImage.obj
            ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB')))).map
      (KernelIdeal.ι (pulledStructureMap f (sameSiteToposHom t)))) ≫
      cokernel.π (inverseImageIdeal_toUnitBase t f) = 0 :=
  sorry

/-- Reverse of `KernelIdeal.additiveLift` for `pulledStructureMap f (sameSiteToposHom t)`: the unique factorization of
the kernel-ideal inclusion through `inverseImageIdeal_toUnitBase`. -/
private def inverseImageIdeal_additiveLiftBase_inv :
    (SheafOfModules.toSheaf
        (ringSheaf JC
          (f.toTopos.commRingInverseImage.obj
            ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB')))).obj
      (KernelIdeal.sheaf (pulledStructureMap f (sameSiteToposHom t))) ⟶
      (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) :=
  CategoryTheory.Abelian.monoLift (inverseImageIdeal_toUnitBase t f)
    ((SheafOfModules.toSheaf
        (ringSheaf JC
          (f.toTopos.commRingInverseImage.obj
            ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB')))).map
      (KernelIdeal.ι (pulledStructureMap f (sameSiteToposHom t))))
    (inverseImageIdeal_ι_comp_toUnitBase_coker t f)

/-- Kernel-comparison isomorphism of `f⁻¹J` with the kernel module of `pulledStructureMap f (sameSiteToposHom t)`. -/
private def inverseImageIdeal_additiveCompareBaseIso :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ≅
      (SheafOfModules.toSheaf
          (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal
          (pulledStructureMap f (sameSiteToposHom t))) where
  hom := inverseImageIdeal_additiveCompareBase t f
  inv :=
    ((pulledBaseMap_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
        inferInstance).hom ≫
      inverseImageIdeal_additiveLiftBase_inv t f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `inverseImageIdeal_additiveCompareBaseIso` is the additive comparison. -/
private theorem inverseImageIdeal_additiveCompareBaseIso_hom :
    (inverseImageIdeal_additiveCompareBaseIso t f).hom =
      inverseImageIdeal_additiveCompareBase t f :=
  sorry

/-- Additive reverse comparison of `Ker(pulledBaseMap)` with `f⁻¹J`. -/
private def inverseImageIdeal_additiveCompareBase_inv :
    (SheafOfModules.toSheaf
        (ringSheaf JC (f.toTopos.commRingInverseImage.obj OB))).obj
      (SheafOfModules.RingedSite.FirstOrderThickening.ideal
        (pulledStructureMap f (sameSiteToposHom t))) ⟶
      (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) :=
  (inverseImageIdeal_additiveCompareBaseIso t f).inv

/-- Module reverse comparison `Ker(pulledBaseMap) ⟶ f⁻¹J`. -/
private def inverseImageIdealCompareBase_inv :
    SheafOfModules.RingedSite.FirstOrderThickening.ideal
        (pulledStructureMap f (sameSiteToposHom t)) ⟶
      inverseImageIdeal f t where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{u}).map
        (inverseImageIdeal_additiveCompareBase_inv t f))
      (fun _ _ _ ↦ sorry)

/-- The coefficient map of `pulledStructureMap f (sameSiteToposHom t)`, as a map out of `Ker(pulledBaseMap)`. -/
@[no_expose] def coeffPulledBase :
    (pulledBaseMap_isFirstOrderThickening t f).isSquareZero.targetModule
        (KernelIdeal.quotientComparison_isIso
          (pulledStructureMap f (sameSiteToposHom t))) ⟶
      (restrictionAlong (commRingStructureMap f)).obj G :=
  inverseImageIdealCompareBase_inv t f ≫ c ≫ (restrictScalarsCompare f G).hom

/-- The tautological Ext¹ class of `pulledStructureMap f (sameSiteToposHom t)` after the coefficient map `c`. -/
def xiPrimeNaive :
    Ext⁽(1 : ℤ)⁾((SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap f)).obj
        (DerivedCategory.Q.obj
          (NaiveCotangent.obj
            (f.toTopos.commRingInverseImage.obj ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB'))
            (Under.mk (pulledStructureMap f (sameSiteToposHom t))))),
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj G)) :=
  SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
    (extendCoeff (pulledStructureMap f (sameSiteToposHom t))
      (pulledBaseMap_isFirstOrderThickening t f).isSquareZero (commRingStructureMap f) G
      (coeffPulledBase t f G c))
    (selfExtensionClass (pulledStructureMap f (sameSiteToposHom t))
      (pulledBaseMap_isFirstOrderThickening t f).isSquareZero)

/-- Cochain map `L(pulledBaseMap) ⟶ NL(pulledBaseMap)`. -/
def toNaivePulledBase :
    CotangentComplex.obj
        (f.toTopos.commRingInverseImage.obj ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB'))
        (Under.mk (pulledStructureMap f (sameSiteToposHom t))) ⟶
      NaiveCotangent.obj
        (f.toTopos.commRingInverseImage.obj ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB'))
        (Under.mk (pulledStructureMap f (sameSiteToposHom t))) :=
  CotangentComplex.toNaive
    (f.toTopos.commRingInverseImage.obj ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB'))
    (Under.mk (pulledStructureMap f (sameSiteToposHom t)))

/-- Comparison `Lf^* L[t] ⟶ Lf^* NL[t]` obtained from `toNaive` of `pulledStructureMap f (sameSiteToposHom t)`. -/
def toPullbackNaive :
    pullbackCotangent f (sameSiteToposHom t) ⟶
      (SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap f)).obj
        (DerivedCategory.Q.obj
          (NaiveCotangent.obj
            (f.toTopos.commRingInverseImage.obj ((sameSiteToposHom t).toTopos.commRingInverseImage.obj OB'))
            (Under.mk (pulledStructureMap f (sameSiteToposHom t))))) :=
  (CotangentComplex.tensorDerivedIso
    (pulledStructureMap f (sameSiteToposHom t)) (commRingStructureMap f)).inv ≫
    (SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap f)).map
      (DerivedCategory.Q.map (toNaivePulledBase t f))

/-- The canonical Ext¹ class ξ' of `Lf^* L[t]` with coefficients `G`. -/
def xiPrime :
    Ext⁽(1 : ℤ)⁾(pullbackCotangent f (sameSiteToposHom t), coeffSingle G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
    (xiPrimeNaive t f G c) (add_zero (1 : ℤ))

/-- `xiPrime` is the image of the tautological class of `t` along `c`, transported
from `NL` to `L`. -/
theorem xiPrime_spec :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
          (extendCoeff (pulledStructureMap f (sameSiteToposHom t))
            (pulledBaseMap_isFirstOrderThickening t f).isSquareZero (commRingStructureMap f) G
            (coeffPulledBase t f G c))
          (selfExtensionClass (pulledStructureMap f (sameSiteToposHom t))
            (pulledBaseMap_isFirstOrderThickening t f).isSquareZero))
        (add_zero (1 : ℤ)) :=
  sorry

/-- The canonical Ext² existence obstruction of the two-site first-order deformation equation. -/
def existenceObstruction :
    Ext⁽(2 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G) :=
  ShiftedHom.comp
    (RingedSite.ToposHom.connectingMap f (sameSiteToposHom t))
    (xiPrime t f G c) rfl

/-- `existenceObstruction` is the connecting image of the tautological class of `t` along `c`. -/
theorem existenceObstruction_spec :
    existenceObstruction t f G c =
      ShiftedHom.comp
        (RingedSite.ToposHom.connectingMap f (sameSiteToposHom t))
        (ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
          (xiPrimeNaive t f G c) (add_zero (1 : ℤ))) rfl :=
  sorry

/-- The cotangent obstruction vanishes exactly when a compatible first-order deformation exists. -/
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction t f G c = 0 ↔ Nonempty (Solution t f G c) := sorry

end RingedSite.FirstOrderThickening
