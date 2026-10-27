/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Solution
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension
public import Mathlib.Data.Setoid.Basic

/-!
# Isomorphism classes of geometric first-order deformation solutions

Forgetting a prescribed kernel map retains a square-zero algebra extension over the
composite inverse-image base. Its extension isomorphism classes define solution classes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf.InternalCommRing
open SheafOfModules.RingedSite
open RingedSite.ToposHom
open SheafOfModules.RingedSite.FirstOrderThickening (sameSiteToposHom)

noncomputable section

universe u

namespace RingedSite.FirstOrderThickening.Solution

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

/-- Forget the prescribed kernel map while retaining the algebra over the composite
inverse-image base, the quotient sheaf, and the identified kernel. -/
def toAlgebraExtension (S : Solution t f G c) :
    AlgebraExtension (f.comp (sameSiteToposHom t)) G where
  middle := S.middle
  proj := S.π
  proj_locallySurjective := S.isFirstOrder.isLocallySurjective
  proj_squareZero := S.isFirstOrder.isSquareZero
  proj_quotient_isIso :=
    @KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _ S.π _
      S.isFirstOrder.isLocallySurjective
  structureMap := CommRingSheaves.fullyFaithfulForgetRing.preimage
    ((f.comp (sameSiteToposHom t)).toTopos.commRingInverseImageForgetRingIso.hom.app OB' ≫
      (MorphismOfTopoiIn.ringInverseImageCompIso (MorphismOfTopoiIn.id JB) f.toTopos).hom.app
        (ringSheaf JB OB') ≫
      f.toTopos.ringInverseImage.map
        (MorphismOfTopoiIn.ringInverseImageIdIso.hom.app (ringSheaf JB OB')) ≫
      S.fromInverseImage)
  commutes := sorry
  kernelIso := S.kernelIso
  induces_c := sorry

/-- Two geometric solutions are equivalent when their underlying algebra extensions
are isomorphic over the base algebra, quotient, and identified kernel. -/
def isoSetoid : Setoid (Solution t f G c) :=
  Setoid.ker (fun S : Solution t f G c ↦
    SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassMk
      (toAlgebraExtension t f G c S))

/-- Isomorphism classes of solutions with the prescribed map on kernels. -/
abbrev IsoClass := Quotient (isoSetoid t f G c)

/-- The isomorphism class represented by a geometric solution. -/
def isoClassMk (S : Solution t f G c) : IsoClass t f G c :=
  Quotient.mk (isoSetoid t f G c) S

/-- Forgetting the prescribed kernel map descends to underlying algebra-extension classes. -/
def forgetIsoClass (p : IsoClass t f G c) :
    SheafOfModules.RingedSite.FirstOrderThickening.Solution.IsoClass
      (𝟙 ((f.comp (sameSiteToposHom t)).toTopos.commRingInverseImage.obj OB'))
      (SheafOfModules.RingedSite.FirstOrderThickening.Solution.isSquareZero_id _)
      (commRingStructureMap (f.comp (sameSiteToposHom t))) G
      (SheafOfModules.RingedSite.FirstOrderThickening.Solution.zeroKernelMap
        (commRingStructureMap (f.comp (sameSiteToposHom t))) G) :=
  Setoid.kerLift (fun S : Solution t f G c ↦
    SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassMk
      (toAlgebraExtension t f G c S)) p

/-- Forgetting a represented solution class gives the class of its underlying algebra extension. -/
theorem forgetIsoClass_mk (S : Solution t f G c) :
    forgetIsoClass t f G c (isoClassMk t f G c S) =
      SheafOfModules.RingedSite.FirstOrderThickening.Solution.isoClassMk
        (toAlgebraExtension t f G c S) := sorry

end RingedSite.FirstOrderThickening.Solution
