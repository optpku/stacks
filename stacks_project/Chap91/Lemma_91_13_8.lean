/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Fiber
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Fiber
import StacksCheckRecall

/-!
# Isomorphism classes of first-order ringed-topos solutions

For an arbitrary geometric morphism into the base of a first-order thickening,
solution classes form the fibre of the naive-cotangent Ext¹ comparison over the
transported tautological extension class.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open RingedSite RingedSite.ToposHom
open RingedSite.FirstOrderThickening
open RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.FirstOrderThickening (sameSiteToposHom)
open scoped DerivedExt RingedSite.ToposHom

noncomputable section

universe u

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

/- Lemma 91.13.8. For a first-order thickening `t`, an arbitrary morphism of ringed
topoi `f`, a module `G`, and the prescribed inverse-image kernel map `c`, solution
isomorphism classes are canonically bijective to the Ext¹ fibre over the image
of the tautological extension class. -/
@[stacks 0GQ9] #check
  (RingedSite.FirstOrderThickening.Solution.isoClassFiberEquiv t f G c :
    IsoClass t f G c ≃
      {ζ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC O))).obj
          NL[f.comp (sameSiteToposHom t)],
          (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC O))).obj
            ((CochainComplex.singleFunctor _ 0).obj G)) //
        NaiveCotangent.extOneComap (sameSiteToposHom t) f ζ =
          NaiveCotangent.extOneMap (sameSiteToposHom t) f (cPull t f G c)
            (selfExtensionClass t)})
