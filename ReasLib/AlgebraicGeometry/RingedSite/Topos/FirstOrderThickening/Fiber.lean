/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.IsoClass
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.NaiveCotangent.Functoriality

/-!
# Geometric Ext fibres of first-order deformation solutions

The cotangent comparison classifies solutions with a prescribed map on kernels by the
fibre over the pullback-and-coefficient image of the tautological extension class.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open RingedSite.ToposHom
open SheafOfModules.RingedSite.FirstOrderThickening (sameSiteToposHom)
open scoped DerivedExt RingedSite.ToposHom

noncomputable section

universe u

namespace RingedSite.FirstOrderThickening.Solution

-- Local instance justification (defeq pin): the geometric Ext comparison and extension classification must use the same standard module derived category.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation selects that same standard localization.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {B : Type u} [Category.{u} B] {JB : GrothendieckTopology B}
variable [JB.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JB.HasSheafCompose (forget RingCat.{u})]
variable [JB.HasSheafCompose (forget CommRingCat.{u})]
variable [JB.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JB CommRingCat.{u}] [JB.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JB AddCommGrpCat.{u}] [JB.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OB OB' : Sheaf JB CommRingCat.{u}}
variable {C : Type u} [Category.{u} C] {JC : GrothendieckTopology C}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}] [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}] [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf JC CommRingCat.{u}}

variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/-- The tautological algebra extension has middle ring sheaf `OB'`, projection `t`,
and its kernel identified with the kernel ideal of `t`. -/
def selfAlgebraExtension :
    AlgebraExtension (sameSiteToposHom t)
      (SheafOfModules.RingedSite.FirstOrderThickening.ideal t) where
  middle := OB'
  proj := t
  proj_locallySurjective := inferInstance
  proj_squareZero := (inferInstance : IsFirstOrderThickening t).isSquareZero
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso t
  structureMap := CommRingSheaves.fullyFaithfulForgetRing.preimage
    ((sameSiteToposHom t).toTopos.commRingInverseImageForgetRingIso.hom.app OB' ≫
      MorphismOfTopoiIn.ringInverseImageIdIso.hom.app (ringSheaf JB OB'))
  commutes := sorry
  kernelIso := Iso.refl _
  induces_c := sorry

/-- The canonical Ext¹ class of the tautological algebra extension. -/
def selfExtensionClass :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JB OB))).obj
      NL[sameSiteToposHom t],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JB OB))).obj
        ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.RingedSite.FirstOrderThickening.ideal t))) :=
  AlgebraExtension.extClass (sameSiteToposHom t) (selfAlgebraExtension t)

/-- The O-linear adjunct of the prescribed inverse-image kernel map. -/
def cPull :
    f.modulePullback.obj (SheafOfModules.RingedSite.FirstOrderThickening.ideal t) ⟶ G :=
  (ModulePullback.scalarHomEquiv f (inverseImageIdeal f t) G).symm c

/-- The canonical Ext¹ class of the underlying algebra extension of a solution class. -/
def toExtClass (p : IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC O))).obj
      NL[f.comp (sameSiteToposHom t)],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC O))).obj
        ((CochainComplex.singleFunctor _ 0).obj G)) :=
  SheafOfModules.RingedSite.FirstOrderThickening.Solution.extensionClass
    (commRingStructureMap (f.comp (sameSiteToposHom t))) G (forgetIsoClass t f G c p)

/-- On a represented solution, the class map is the canonical algebra-extension class. -/
theorem toExtClass_mk (S : Solution t f G c) :
    toExtClass t f G c (isoClassMk t f G c S) =
      AlgebraExtension.extClass (f.comp (sameSiteToposHom t))
        (toAlgebraExtension t f G c S) := sorry

/-- The geometric Ext fibre over the transported tautological extension class. -/
abbrev solutionExtFiber :=
  {ζ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC O))).obj
      NL[f.comp (sameSiteToposHom t)],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC O))).obj
        ((CochainComplex.singleFunctor _ 0).obj G)) //
    NaiveCotangent.extOneComap (sameSiteToposHom t) f ζ =
      NaiveCotangent.extOneMap (sameSiteToposHom t) f (cPull t f G c)
        (selfExtensionClass t)}

/-- A fibre representative maps to the transported tautological extension class. -/
theorem mem_solutionExtFiber (ζ : solutionExtFiber t f G c) :
    NaiveCotangent.extOneComap (sameSiteToposHom t) f ζ.val =
      NaiveCotangent.extOneMap (sameSiteToposHom t) f (cPull t f G c)
        (selfExtensionClass t) := sorry

/-- The canonical class of a solution belongs to the prescribed geometric Ext fibre. -/
theorem toExtClass_mem (p : IsoClass t f G c) :
    NaiveCotangent.extOneComap (sameSiteToposHom t) f (toExtClass t f G c p) =
      NaiveCotangent.extOneMap (sameSiteToposHom t) f (cPull t f G c)
        (selfExtensionClass t) := sorry

/-- The canonical forward map from geometric solution classes to the prescribed Ext fibre. -/
def toFiber (p : IsoClass t f G c) : solutionExtFiber t f G c :=
  ⟨toExtClass t f G c p, toExtClass_mem t f G c p⟩

/-- The canonical forward map from geometric solution classes to the Ext fibre is bijective. -/
theorem toFiber_bijective : Function.Bijective (toFiber t f G c) := sorry

/-- Geometric solution classes are canonically equivalent to the prescribed Ext fibre. -/
def isoClassFiberEquiv : IsoClass t f G c ≃ solutionExtFiber t f G c :=
  Equiv.ofBijective (toFiber t f G c) (toFiber_bijective t f G c)

/-- The equivalence sends a solution class to its canonical extension class. -/
theorem isoClassFiberEquiv_apply (p : IsoClass t f G c) :
    (isoClassFiberEquiv t f G c p).val = toExtClass t f G c p := sorry

/-- The inverse equivalence recovers a solution class with the specified extension class. -/
theorem isoClassFiberEquiv_symm_apply (ζ : solutionExtFiber t f G c) :
    toExtClass t f G c ((isoClassFiberEquiv t f G c).symm ζ) = ζ.val := sorry

/-- Solutions exist exactly when the prescribed geometric Ext fibre is inhabited. -/
theorem isoClassFiberEquiv_nonempty_iff :
    Nonempty (IsoClass t f G c) ↔ Nonempty (solutionExtFiber t f G c) := sorry

end RingedSite.FirstOrderThickening.Solution
