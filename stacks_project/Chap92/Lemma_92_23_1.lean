/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.CotangentTorsor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.FittingIso
import StacksCheckRecall

/-!
# Deformations of ringed topoi and the cotangent complex

In the first-order thickening situation of 92.23.0.1, solutions are governed by
Ext⁽n⁾ with first argument `commRingCotangentComplex f`: a canonical class ξ in Ext⁽2⁾ vanishes iff a solution exists;
isomorphism classes of solutions are principal homogeneous under Ext⁽1⁾;
automorphisms of a given solution fitting the diagram are Ext⁽0⁾.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DerivedCategory
open CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open RingedSite.FirstOrderThickening
open RingedSite.ToposHom
open SheafOfModules.RingedSite.CotangentComplex (coeffSingle)
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

variable {O : Sheaf JC CommRingCat.{u}}
variable {OB OB' : Sheaf JD CommRingCat.{u}}
variable (t : OB' ⟶ OB) [IsFirstOrderThickening t]
variable (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JD OB))
variable (G : SheafOfModules.{u} (ringSheaf JC O))
variable (c : inverseImageIdeal f t ⟶ (SheafOfModules.restrictScalars f.structureMap).obj G)

/- Lemma 92.23.1 (1). The canonical Ext² obstruction vanishes if and only if a solution
of the first-order deformation equation exists. -/
@[stacks 08V5] #check (RingedSite.FirstOrderThickening.existenceObstruction_eq_zero_iff t f G c :
  RingedSite.FirstOrderThickening.existenceObstruction t f G c = 0 ↔
    Nonempty (RingedSite.FirstOrderThickening.Solution t f G c))

/- Lemma 92.23.1 (2). If a solution exists, its isomorphism classes form a principal
homogeneous space under Ext¹ of the cotangent complex. -/
@[stacks 08V5] #check (RingedSite.FirstOrderThickening.derivedAddTorsor t f G c :
  RingedSite.FirstOrderThickening.Solution t f G c →
    AddTorsor
      (Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G))
      (RingedSite.FirstOrderThickening.Solution.IsoClass t f G c))

/- Lemma 92.23.1 (3). The fitting automorphisms of each solution are canonically
identified with Ext⁰ of the cotangent complex. -/
@[stacks 08V5] #check (RingedSite.FirstOrderThickening.autEquiv t f G c :
  ∀ S : RingedSite.FirstOrderThickening.Solution t f G c,
    Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G) ≃
      RingedSite.FirstOrderThickening.SolutionIso S S)

#check (RingedSite.FirstOrderThickening.isoClassDerivedEquiv t f G c :
  RingedSite.FirstOrderThickening.Solution t f G c →
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G) ≃
      RingedSite.FirstOrderThickening.Solution.IsoClass t f G c)

#check (RingedSite.FirstOrderThickening.derivedVAdd_spec t f G c :
  ∀ (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (commRingCotangentComplex f), coeffSingle G))
    (p q : RingedSite.FirstOrderThickening.Solution.IsoClass t f G c),
    RingedSite.FirstOrderThickening.derivedVAdd t f G c ξ p = q ↔
      RingedSite.FirstOrderThickening.derivedVSub t f G c q p = ξ)

end RingedSite.FirstOrderThickening
