/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Cochain
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.NaiveComparison
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap91.Lemma_91_13_8_Extension
public import stacks_project.Chap92.Lemma_92_22_2
public import stacks_project.Chap92.Lemma_92_22_3_Triangle
public import stacks_project.Chap92.Lemma_92_22_4
public import stacks_project.Chap92.«92_23_0_1_Solution»

/-!
# Cotangent Ext² existence obstruction of a first-order thickening of ringed topoi

A first-order thickening t : O_{B'} ⟶ O_B, a morphism f of ringed topoi, an O-module G,
and a map c : f⁻¹J ⟶ G determine a canonical class in Ext⁽2⁾(Q L[f], Q(G[0])). The class
is the connecting image of the tautological Ext¹ class of Lf^* L[t] along the transitivity
triangle of f and t.
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

-- Local instance justification (defeq pin): moduleCategoryHasDerivedCategory is the reducible
-- standard HasDerivedCategory owner used by 92.22.3 and 91.13.*; Ext, Q, and singleFunctor must
-- share that instance.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): moduleCat_hasDerivedCategory is reducible to
-- HasDerivedCategory.standard and is not global; ModuleDerived, singleFunctor, and Ext must share
-- that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/-- The same-site morphism of ringed topoi associated to a first-order thickening `t`, identity
on underlying topoi, with structure map induced by `t`. -/
def thickeningToposHom :
    ToposHom (ofCommRingSheaf JD OB) (ofCommRingSheaf JD OB') where
  toTopos := MorphismOfTopoiIn.id JD
  structureMap :=
    (MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := JD)).hom.app (ringSheaf JD OB') ≫
      ringSheafMap t

/-- The underlying morphism of topoi of `thickeningToposHom` is the identity. -/
theorem thickeningToposHom_toTopos :
    (thickeningToposHom t).toTopos = MorphismOfTopoiIn.id JD :=
  sorry

/-- Unfolding of the structure map of `thickeningToposHom`. -/
theorem thickeningToposHom_eq :
    (thickeningToposHom t).structureMap =
      (MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := JD)).hom.app (ringSheaf JD OB') ≫
        ringSheafMap t :=
  sorry

/-- Identity inverse image of `O_{B'}` recovers `O_{B'}` on the target site. -/
def thickeningSourceIso :
    inverseImageStructureSheaf (thickeningToposHom t) ≅ OB' :=
  InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimageIso
    ((inverseImageStructureSheaf_ring (thickeningToposHom t)) ≪≫
      (MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := JD)).app (ringSheaf JD OB'))

/-- Unfolding of `thickeningSourceIso` as the identity inverse-image comparison. -/
theorem thickeningSourceIso_eq :
    thickeningSourceIso t =
      InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimageIso
        ((inverseImageStructureSheaf_ring (thickeningToposHom t)) ≪≫
          (MorphismOfTopoiIn.ringInverseImageIdIso (J₀ := JD)).app (ringSheaf JD OB')) :=
  sorry

/-- Inverse image of `t` as a commutative ring-sheaf map on the source site of `f`. -/
def pulledThickening : (inverseImageCommRing f).obj OB' ⟶ (inverseImageCommRing f).obj OB :=
  (inverseImageCommRing f).map t

/-- Unfolding of `pulledThickening` as inverse image of `t`. -/
theorem pulledThickening_eq :
    pulledThickening t f = (inverseImageCommRing f).map t :=
  sorry

/-- Inverse image along `f` preserves first-order thickenings. -/
instance pulled_isFirstOrderThickening :
    IsFirstOrderThickening (pulledThickening t f) :=
  sorry

/-- Inverse image of `thickeningSourceIso.inv` along `f`. -/
def pulledSourceMap :
    (inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)) ⟶
      (inverseImageCommRing f).obj OB' :=
  (inverseImageCommRing f).map (thickeningSourceIso t).hom

/-- Unfolding of `pulledSourceMap`. -/
theorem pulledSourceMap_eq :
    pulledSourceMap t f = (inverseImageCommRing f).map (thickeningSourceIso t).hom :=
  sorry

/-- After the identity inverse-image comparison, `pulledBaseMap` is `pulledSourceMap ≫ pulledThickening`. -/
theorem pulledBaseMap_eq_composite :
    pulledBaseMap f (thickeningToposHom t) =
      pulledSourceMap t f ≫ pulledThickening t f :=
  sorry

/-- The coefficient object `Q(G[0])` in `D(O)`. -/
abbrev coeffSingle : DerivedCategory (SheafOfModules (ringSheaf JC O)) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)

/-- Unfolding of `coeffSingle` as the derived image of the degree-zero single complex. -/
theorem coeffSingle_eq :
    coeffSingle G =
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G) :=
  sorry

/-- Additive comparison of `f⁻¹J` with the kernel of `pulledThickening`. -/
def inverseImageIdeal_additiveCompare :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC ((inverseImageCommRing f).obj OB))).obj
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
            (ringSheaf JC ((inverseImageCommRing f).obj OB'))).map
          (KernelIdeal.ι (pulledThickening t f))) ≫
      SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t) = 0 :=
  sorry

/-- Additive reverse comparison of `Ker(pulled t)` with the kernel of the inverse-image ring
map of `t`. -/
def inverseImageIdeal_additiveCompare_inv :
    (SheafOfModules.toSheaf (ringSheaf JC ((inverseImageCommRing f).obj OB))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal (pulledThickening t f)) ⟶
      kernel (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) :=
  kernel.lift (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t))
    (((pulled_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
        inferInstance).hom ≫
      (SheafOfModules.toSheaf
          (ringSheaf JC ((inverseImageCommRing f).obj OB'))).map
        (KernelIdeal.ι (pulledThickening t f)))
    (pulled_ι_comp_unitUnderlyingMap t f)

/-- Canonical kernel lift of the additive inclusion of `f⁻¹J`. -/
def inverseImageIdeal_toKernel :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      kernel (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t)) :=
  kernel.lift (SheafOfModules.unitUnderlyingMap (inverseImageRingMap f t))
    (inverseImageIdeal_toUnit f t)
    (inverseImageIdeal_toUnit_comp_unitUnderlyingMap t f)

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
`structureSheafMap f`. -/
def restrictScalarsCompare :
    (SheafOfModules.restrictScalars f.structureMap).obj G ≅
      (restrictionAlong (structureSheafMap f)).obj G :=
  Iso.refl _

/-- The coefficient map of the pulled same-site equation, as a map out of `Ker(pulled t)`. -/
def coeffSameSite :
    (pulled_isFirstOrderThickening t f).isSquareZero.targetModule
        (KernelIdeal.quotientComparison_isIso (pulledThickening t f)) ⟶
      (restrictionAlong (structureSheafMap f)).obj G :=
  (inverseImageIdealIso t f).inv ≫ c ≫ (restrictScalarsCompare f G).hom

/-- `coeffSameSite` is the transport of `c` along `inverseImageIdealIso` and
`restrictScalarsCompare`. -/
theorem coeffSameSite_eq :
    coeffSameSite t f G c =
      (inverseImageIdealIso t f).inv ≫ c ≫ (restrictScalarsCompare f G).hom :=
  sorry

/-- The tautological Ext¹ class of `t` after inverse image along `f` and the coefficient map `c`. -/
def xiPrimeSameSite :
    Ext⁽(1 : ℤ)⁾((SheafOfModules.RingedSite.SameSite.pullbackDerived (structureSheafMap f)).obj
        ((SheafOfModules.RingedSite.FirstOrderThickening.moduleQ
            ((inverseImageCommRing f).obj OB)).obj
          (NaiveCotangent.obj ((inverseImageCommRing f).obj OB')
            (Under.mk (pulledThickening t f)))),
      (SheafOfModules.RingedSite.FirstOrderThickening.moduleQ O).obj
        ((CochainComplex.singleFunctor _ 0).obj G)) :=
  SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
    (extendCoeff (pulledThickening t f)
      (pulled_isFirstOrderThickening t f).isSquareZero (structureSheafMap f) G
      (coeffSameSite t f G c))
    (selfExtensionClass (pulledThickening t f)
      (pulled_isFirstOrderThickening t f).isSquareZero)

/-- `xiPrimeSameSite` is `extOne_map` of `selfExtensionClass` of the pulled thickening along
`coeffSameSite`. -/
theorem xiPrimeSameSite_eq :
    xiPrimeSameSite t f G c =
      SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
        (extendCoeff (pulledThickening t f)
          (pulled_isFirstOrderThickening t f).isSquareZero (structureSheafMap f) G
          (coeffSameSite t f G c))
        (selfExtensionClass (pulledThickening t f)
          (pulled_isFirstOrderThickening t f).isSquareZero) :=
  sorry

/-- Inverse image along `f` of the identity thickening of `t` remains first-order. -/
instance pulledBaseMap_isFirstOrderThickening :
    IsFirstOrderThickening (pulledBaseMap f (thickeningToposHom t)) :=
  sorry

/-- Additive inclusion of `f⁻¹J` into the unit of the source of `pulledBaseMap`. -/
def inverseImageIdeal_toUnitBase :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf
          (ringSheaf JC
            ((inverseImageCommRing f).obj
              (inverseImageStructureSheaf (thickeningToposHom t))))).obj
        (SheafOfModules.unit
          (ringSheaf JC
            ((inverseImageCommRing f).obj
              (inverseImageStructureSheaf (thickeningToposHom t))))) :=
  inverseImageIdeal_toUnit f t ≫
    SheafOfModules.unitUnderlyingMap
      (ringSheafMap ((inverseImageCommRing f).map (thickeningSourceIso t).inv))

/-- The inclusion of `f⁻¹J` is killed by `pulledBaseMap`. -/
theorem inverseImageIdeal_toUnitBase_comp :
    inverseImageIdeal_toUnitBase t f ≫
      SheafOfModules.unitUnderlyingMap
        (ringSheafMap (pulledBaseMap f (thickeningToposHom t))) = 0 :=
  sorry

/-- Additive comparison of `f⁻¹J` with the kernel of `pulledBaseMap`. -/
def inverseImageIdeal_additiveCompareBase :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ⟶
      (SheafOfModules.toSheaf
          (ringSheaf JC (inverseImageStructureSheaf f))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal
          (pulledBaseMap f (thickeningToposHom t))) :=
  KernelIdeal.additiveLift (pulledBaseMap f (thickeningToposHom t))
    (inverseImageIdeal_toUnitBase t f) (inverseImageIdeal_toUnitBase_comp t f) ≫
    ((pulledBaseMap_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
      inferInstance).inv

/-- Module comparison `f⁻¹J ⟶ Ker(pulledBaseMap)`. -/
def inverseImageIdealCompareBase :
    inverseImageIdeal f t ⟶
      SheafOfModules.RingedSite.FirstOrderThickening.ideal
        (pulledBaseMap f (thickeningToposHom t)) where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{u}).map
        (inverseImageIdeal_additiveCompareBase t f))
      (fun _ _ _ ↦ sorry)

/-- The additive inclusion of `f⁻¹J` into the source of `pulledBaseMap` is a monomorphism. -/
instance inverseImageIdeal_toUnitBase_mono :
    Mono (inverseImageIdeal_toUnitBase t f) :=
  sorry

/-- The kernel-ideal inclusion of `pulledBaseMap` vanishes on the cokernel of
`inverseImageIdeal_toUnitBase`. -/
theorem inverseImageIdeal_ι_comp_toUnitBase_coker :
    ((SheafOfModules.toSheaf
        (ringSheaf JC
          ((inverseImageCommRing f).obj
            (inverseImageStructureSheaf (thickeningToposHom t))))).map
      (KernelIdeal.ι (pulledBaseMap f (thickeningToposHom t)))) ≫
      cokernel.π (inverseImageIdeal_toUnitBase t f) = 0 :=
  sorry

/-- Reverse of `KernelIdeal.additiveLift` for `pulledBaseMap`: the unique factorization of
the kernel-ideal inclusion through `inverseImageIdeal_toUnitBase`. -/
def inverseImageIdeal_additiveLiftBase_inv :
    (SheafOfModules.toSheaf
        (ringSheaf JC
          ((inverseImageCommRing f).obj
            (inverseImageStructureSheaf (thickeningToposHom t))))).obj
      (KernelIdeal.sheaf (pulledBaseMap f (thickeningToposHom t))) ⟶
      (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) :=
  CategoryTheory.Abelian.monoLift
    (inverseImageIdeal_toUnitBase t f)
    ((SheafOfModules.toSheaf
        (ringSheaf JC
          ((inverseImageCommRing f).obj
            (inverseImageStructureSheaf (thickeningToposHom t))))).map
      (KernelIdeal.ι (pulledBaseMap f (thickeningToposHom t))))
    (inverseImageIdeal_ι_comp_toUnitBase_coker t f)

/-- Kernel-comparison isomorphism of `f⁻¹J` with the kernel module of `pulledBaseMap`. -/
def inverseImageIdeal_additiveCompareBaseIso :
    (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) ≅
      (SheafOfModules.toSheaf
          (ringSheaf JC (inverseImageStructureSheaf f))).obj
        (SheafOfModules.RingedSite.FirstOrderThickening.ideal
          (pulledBaseMap f (thickeningToposHom t))) where
  hom := inverseImageIdeal_additiveCompareBase t f
  inv :=
    ((pulledBaseMap_isFirstOrderThickening t f).isSquareZero.targetModuleForgetIso
        inferInstance).hom ≫
      inverseImageIdeal_additiveLiftBase_inv t f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `inverseImageIdeal_additiveCompareBaseIso` is the additive comparison. -/
theorem inverseImageIdeal_additiveCompareBaseIso_hom :
    (inverseImageIdeal_additiveCompareBaseIso t f).hom =
      inverseImageIdeal_additiveCompareBase t f :=
  sorry

/-- Additive reverse comparison of `Ker(pulledBaseMap)` with `f⁻¹J`. -/
def inverseImageIdeal_additiveCompareBase_inv :
    (SheafOfModules.toSheaf
        (ringSheaf JC (inverseImageStructureSheaf f))).obj
      (SheafOfModules.RingedSite.FirstOrderThickening.ideal
        (pulledBaseMap f (thickeningToposHom t))) ⟶
      (SheafOfModules.toSheaf (inverseImageRing f OB)).obj (inverseImageIdeal f t) :=
  (inverseImageIdeal_additiveCompareBaseIso t f).inv

/-- Module reverse comparison `Ker(pulledBaseMap) ⟶ f⁻¹J`. -/
def inverseImageIdealCompareBase_inv :
    SheafOfModules.RingedSite.FirstOrderThickening.ideal
        (pulledBaseMap f (thickeningToposHom t)) ⟶
      inverseImageIdeal f t where
  val :=
    PresheafOfModules.homMk
      ((sheafToPresheaf JC AddCommGrpCat.{u}).map
        (inverseImageIdeal_additiveCompareBase_inv t f))
      (fun _ _ _ ↦ sorry)

/-- The coefficient map of `pulledBaseMap`, as a map out of `Ker(pulledBaseMap)`. -/
def coeffPulledBase :
    (pulledBaseMap_isFirstOrderThickening t f).isSquareZero.targetModule
        (KernelIdeal.quotientComparison_isIso
          (pulledBaseMap f (thickeningToposHom t))) ⟶
      (restrictionAlong (structureSheafMap f)).obj G :=
  inverseImageIdealCompareBase_inv t f ≫ c ≫ (restrictScalarsCompare f G).hom

/-- The tautological Ext¹ class of `pulledBaseMap` after the coefficient map `c`. -/
def xiPrimeNaive :
    Ext⁽(1 : ℤ)⁾((SheafOfModules.RingedSite.SameSite.pullbackDerived (structureSheafMap f)).obj
        ((SheafOfModules.RingedSite.FirstOrderThickening.moduleQ
            (inverseImageStructureSheaf f)).obj
          (NaiveCotangent.obj
            ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
            (Under.mk (pulledBaseMap f (thickeningToposHom t))))),
      (SheafOfModules.RingedSite.FirstOrderThickening.moduleQ O).obj
        ((CochainComplex.singleFunctor _ 0).obj G)) :=
  SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
    (extendCoeff (pulledBaseMap f (thickeningToposHom t))
      (pulledBaseMap_isFirstOrderThickening t f).isSquareZero (structureSheafMap f) G
      (coeffPulledBase t f G c))
    (selfExtensionClass (pulledBaseMap f (thickeningToposHom t))
      (pulledBaseMap_isFirstOrderThickening t f).isSquareZero)

/-- `xiPrimeNaive` is `extOne_map` of `selfExtensionClass` of `pulledBaseMap` along `c`. -/
theorem xiPrimeNaive_eq :
    xiPrimeNaive t f G c =
      SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
        (extendCoeff (pulledBaseMap f (thickeningToposHom t))
          (pulledBaseMap_isFirstOrderThickening t f).isSquareZero (structureSheafMap f) G
          (coeffPulledBase t f G c))
        (selfExtensionClass (pulledBaseMap f (thickeningToposHom t))
          (pulledBaseMap_isFirstOrderThickening t f).isSquareZero) :=
  sorry

/-- Cochain map `L(pulledBaseMap) ⟶ NL(pulledBaseMap)`. -/
def toNaivePulledBase :
    CotangentComplex.obj
        ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
        (Under.mk (pulledBaseMap f (thickeningToposHom t))) ⟶
      NaiveCotangent.obj
        ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
        (Under.mk (pulledBaseMap f (thickeningToposHom t))) :=
  CotangentComplex.toNaive
    ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
    (Under.mk (pulledBaseMap f (thickeningToposHom t)))

/-- Unfolding of `toNaivePulledBase`. -/
theorem toNaivePulledBase_eq :
    toNaivePulledBase t f =
      CotangentComplex.toNaive
        ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
        (Under.mk (pulledBaseMap f (thickeningToposHom t))) :=
  sorry

/-- Derived pullback of `NL(pulledBaseMap)` agrees with underived extension of scalars. -/
instance instIsIso_cochainCounit_naivePulledBase :
    IsIso
      ((Functor.LeftDerived.Homotopy.cochainCounit
          ((sameSiteHom (structureSheafMap f)).modulePullback)).app
        (NaiveCotangent.obj
          ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
          (Under.mk (pulledBaseMap f (thickeningToposHom t))))) :=
  sorry

/-- The cochain counit at `NL(pulledBaseMap)`, as an isomorphism. -/
def cochainCounitNaiveIso :
    (SheafOfModules.RingedSite.SameSite.pullbackDerived (structureSheafMap f)).obj
        ((SheafOfModules.RingedSite.FirstOrderThickening.moduleQ
            (inverseImageStructureSheaf f)).obj
          (NaiveCotangent.obj
            ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
            (Under.mk (pulledBaseMap f (thickeningToposHom t))))) ≅
      DerivedCategory.Q.obj
        ((((sameSiteHom (structureSheafMap f)).modulePullback).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (NaiveCotangent.obj
            ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
            (Under.mk (pulledBaseMap f (thickeningToposHom t))))) :=
  @asIso (DerivedCategory (SheafOfModules (ringSheaf JC O))) _ _ _
    ((Functor.LeftDerived.Homotopy.cochainCounit
        ((sameSiteHom (structureSheafMap f)).modulePullback)).app
      (NaiveCotangent.obj
        ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
        (Under.mk (pulledBaseMap f (thickeningToposHom t)))))
    (instIsIso_cochainCounit_naivePulledBase t f)

/-- Comparison `Lf^* L[t] ⟶ Lf^* NL[t]` obtained from `toNaive` of `pulledBaseMap`. -/
def toPullbackNaive :
    pullbackCotangent f (thickeningToposHom t) ⟶
      (SheafOfModules.RingedSite.SameSite.pullbackDerived (structureSheafMap f)).obj
        ((SheafOfModules.RingedSite.FirstOrderThickening.moduleQ
            (inverseImageStructureSheaf f)).obj
          (NaiveCotangent.obj
            ((inverseImageCommRing f).obj (inverseImageStructureSheaf (thickeningToposHom t)))
            (Under.mk (pulledBaseMap f (thickeningToposHom t))))) :=
  DerivedCategory.Q.map
      ((((sameSiteHom (structureSheafMap f)).modulePullback).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (toNaivePulledBase t f)) ≫
    (cochainCounitNaiveIso t f).inv

/-- Unfolding of `toPullbackNaive`. -/
theorem toPullbackNaive_eq :
    toPullbackNaive t f =
      DerivedCategory.Q.map
          ((((sameSiteHom (structureSheafMap f)).modulePullback).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (toNaivePulledBase t f)) ≫
        (cochainCounitNaiveIso t f).inv :=
  sorry

/-- The canonical Ext¹ class ξ' of `Lf^* L[t]` with coefficients `G`. -/
def xiPrime :
    Ext⁽(1 : ℤ)⁾(pullbackCotangent f (thickeningToposHom t), coeffSingle G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
    (xiPrimeNaive t f G c) (add_zero (1 : ℤ))

/-- `xiPrime` is precomposition of `xiPrimeNaive` along `toPullbackNaive`. -/
theorem xiPrime_eq :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (xiPrimeNaive t f G c) (add_zero (1 : ℤ)) :=
  sorry

/-- `xiPrime` is the 91.13.8 image of the tautological class of `t` along `c`, transported
from `NL` to `L`. -/
theorem xiPrime_spec :
    xiPrime t f G c =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
        (SheafOfModules.RingedSite.FirstOrderThickening.extOne_map
          (extendCoeff (pulledBaseMap f (thickeningToposHom t))
            (pulledBaseMap_isFirstOrderThickening t f).isSquareZero (structureSheafMap f) G
            (coeffPulledBase t f G c))
          (selfExtensionClass (pulledBaseMap f (thickeningToposHom t))
            (pulledBaseMap_isFirstOrderThickening t f).isSquareZero))
        (add_zero (1 : ℤ)) :=
  sorry

/-- The canonical Ext² existence obstruction of the two-site first-order deformation equation. -/
def existenceObstruction :
    Ext⁽(2 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G) :=
  ShiftedHom.comp
    (RingedSite.ToposHom.connectingMap f (thickeningToposHom t))
    (xiPrime t f G c) rfl

/-- `existenceObstruction` is `ShiftedHom.comp` of `ToposHom.connectingMap` with `xiPrime`. -/
theorem existenceObstruction_eq :
    existenceObstruction t f G c =
      ShiftedHom.comp
        (RingedSite.ToposHom.connectingMap f (thickeningToposHom t))
        (xiPrime t f G c) rfl :=
  sorry

/-- `existenceObstruction` is the connecting image of the tautological class of `t` along `c`. -/
theorem existenceObstruction_spec :
    existenceObstruction t f G c =
      ShiftedHom.comp
        (RingedSite.ToposHom.connectingMap f (thickeningToposHom t))
        (ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toPullbackNaive t f))
          (xiPrimeNaive t f G c) (add_zero (1 : ℤ))) rfl :=
  sorry

/-- Derived morphism `L[f] ⟶ NL[f]` in `D(O)`. -/
def toNaiveDerived : DerivedCategory.Q.obj L[f] ⟶ DerivedCategory.Q.obj NL[f] :=
  DerivedCategory.Q.map (toNaive f)

/-- Unfolding of `toNaiveDerived` as `Q.map` of `toNaive`. -/
theorem toNaiveDerived_eq :
    toNaiveDerived f = DerivedCategory.Q.map (toNaive f) :=
  sorry

/-- Section `NL[f] ⟶ τ_{≥ -1} L[f]` in `D(O)`, via `πTruncGE`, the truncation
quasi-isomorphism of `toNaive`, and the canonical `qHom` comparison. -/
def toTruncGESection :
    DerivedCategory.Q.obj NL[f] ⟶
      (DerivedCategory.TStructure.t.truncGE (-1)).obj (DerivedCategory.Q.obj L[f]) :=
  DerivedCategory.Q.map (NL[f].πTruncGE (-1)) ≫
    inv (DerivedCategory.Q.map (CochainComplex.truncGEMap (toNaive f) (-1)))
      (I := (DerivedCategory.isIso_Q_map_iff_quasiIso
        (SheafOfModules (ringSheaf JC O)) _).mpr
        (CotangentComplex.toNaive_truncGE_quasiIso
          (f.toTopos.commRingInverseImage.obj OB) (Under.mk (commRingStructureMap f)))) ≫
    inv (@DerivedCategory.TruncGE.qHom (SheafOfModules (ringSheaf JC O)) _ _ _ L[f] (-1))
      (I := @DerivedCategory.TruncGE.qHom_isIso
        (SheafOfModules (ringSheaf JC O)) _ _ _ L[f] (-1))

/-- Unfolding of `toTruncGESection`. -/
theorem toTruncGESection_eq :
    toTruncGESection f =
      DerivedCategory.Q.map (NL[f].πTruncGE (-1)) ≫
        inv (DerivedCategory.Q.map (CochainComplex.truncGEMap (toNaive f) (-1)))
          (I := (DerivedCategory.isIso_Q_map_iff_quasiIso
            (SheafOfModules (ringSheaf JC O)) _).mpr
            (CotangentComplex.toNaive_truncGE_quasiIso
              (f.toTopos.commRingInverseImage.obj OB) (Under.mk (commRingStructureMap f)))) ≫
        inv (@DerivedCategory.TruncGE.qHom (SheafOfModules (ringSheaf JC O)) _ _ _ L[f] (-1))
          (I := @DerivedCategory.TruncGE.qHom_isIso
            (SheafOfModules (ringSheaf JC O)) _ _ _ L[f] (-1)) :=
  sorry

/-- The shifted coefficient object `G[1]` lies in `t.GE (-1)`. -/
instance coeffSingle_shift_isGE :
    DerivedCategory.TStructure.t.IsGE ((coeffSingle G)⟦(1 : ℤ)⟧) (-1) :=
  DerivedCategory.TStructure.t.isGE_shift (coeffSingle G) (0 : ℤ) (1 : ℤ) (-1)

/-- The Ext¹ class of `NL[f]` obtained from a derived Ext¹ class by `descTruncGE`
and `toTruncGESection`. -/
def fromDerivedToNaiveExt
    (η : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G)) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toTruncGESection f))
    (DerivedCategory.TStructure.t.descTruncGE
      (η : DerivedCategory.Q.obj L[f] ⟶ (coeffSingle G)⟦(1 : ℤ)⟧) (-1))
    (add_zero (1 : ℤ))

/-- The naive-to-derived Ext¹ comparison of `NL[f]` with `L[f]`. -/
def extOneTruncEquiv :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G) ≃
      Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G) where
  toFun ξ :=
    ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived f)) ξ (add_zero (1 : ℤ))
  invFun η := fromDerivedToNaiveExt f G η
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extOneTruncEquiv` is precomposition along `toNaiveDerived`. -/
theorem extOneTruncEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj NL[f], coeffSingle G)) :
    extOneTruncEquiv f G ξ =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived f)) ξ
        (add_zero (1 : ℤ)) :=
  sorry

/-- The unshifted morphism `L[f] ⟶ G[0]` attached to a map out of `Ω(structureSheafMap f)`. -/
def homKaehlerDerived (α : Ω(structureSheafMap f) ⟶ G) :
    DerivedCategory.Q.obj L[f] ⟶ coeffSingle G :=
  DerivedCategory.Q.map
    (CotangentComplex.augmentation (structureSheafMap f) ≫
      (CochainComplex.singleFunctor _ 0).map α)

/-- The Hom representative of an Ext⁰ class, obtained from `H^0` along `homologyZeroIso`. -/
def homOfExtZero (e : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G)) :
    Ω(structureSheafMap f) ⟶ G :=
  (homologyZeroIso f).inv ≫
    (DerivedCategory.homologyFunctorFactors (SheafOfModules (ringSheaf JC O)) (0 : ℤ)).inv.app
      L[f] ≫
    (DerivedCategory.homologyFunctor (SheafOfModules (ringSheaf JC O)) (0 : ℤ)).map
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm e) ≫
    (DerivedCategory.homologyFunctorFactors (SheafOfModules (ringSheaf JC O)) (0 : ℤ)).hom.app
      ((CochainComplex.singleFunctor _ 0).obj G) ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) G).hom

/-- The Ext⁰ identification `Hom(Ω(structureSheafMap f), G) ≃ Ext⁽0⁾(Q L[f], Q(G[0]))`. -/
def extZeroHomEquiv :
    (Ω(structureSheafMap f) ⟶ G) ≃
      Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L[f], coeffSingle G) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived f G α)
  invFun e := homOfExtZero f G e
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω(structureSheafMap f) ⟶ G) :
    extZeroHomEquiv f G α =
      ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived f G α) :=
  sorry

end RingedSite.FirstOrderThickening
