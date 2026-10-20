/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KFlatResolution
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Left
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived pullback from K-flat models

For a morphism between commutative ringed-site presentations, pullback inverts
quasi-isomorphisms between K-flat complexes with flat terms.  Such models form a denominator
cover, so they compute the unbounded total left derived pullback.  The public API retains both
the abstract definedness statement and its canonical computation isomorphism.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.modulePushforward.{w}).IsRightAdjoint]
variable [CategoryWithHomology
  (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))]

namespace modulePullbackToDerived

/-- On K-flat homotopy objects with flat terms, module pullback followed by localization
inverts every restricted quasi-isomorphism. -/
@[stacks 06YY "good quasi-isomorphisms"]
theorem isInvertedBy :
    (HomotopyCategory.KFlat.TermwiseFlat.quasiIso
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).IsInvertedBy
        ((HomotopyCategory.KFlat.termwiseFlat
          (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).ι ⋙
            modulePullbackToDerived.{w} f) := sorry

/-- A K-flat homotopy object represented by a complex with flat terms computes module
pullback's total left derived value. -/
@[stacks 06YY "K-flat computation of derived pullback"]
theorem computesAt
    {K : ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)}
    (hK : HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) K) :
    Functor.LeftDerived.ComputesAt
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY)) K := sorry

/-- Module pullback is source-defined at every object because K-flat complexes with flat
terms form a denominator cover. -/
@[stacks 06YY "unbounded derived module pullback", instance]
theorem everywhereDefined :
    Functor.LeftDerived.EverywhereDefined
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY)) := sorry

/-- Module pullback admits its unbounded total left derived functor. -/
@[stacks 06YY "unbounded derived module pullback", instance]
theorem hasLeftDerived :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY)) := sorry

end modulePullbackToDerived

namespace modulePullbackDerived.KFlat

/-- The canonical comparison between derived and ordinary pullback at an object where ordinary
pullback computes the total left derived functor. The computation proof is explicit because it
is used to construct inverse morphism data. -/
@[stacks 06YY "K-flat computation of derived pullback"]
noncomputable def objIso
    {K : ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)}
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
    (h_compute : Functor.LeftDerived.ComputesAt
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY)) K) :
    (modulePullbackDerived.{w} f).obj
        ((moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY)).obj K) ≅
      (modulePullbackToDerived.{w} f).obj K :=
  Functor.LeftDerived.ComputesAt.counitIso
    (modulePullbackToDerived.{w} f)
    (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY)) K
    h_compute

/-- The forward map of `objIso` is the canonical total-left-derived counit. -/
@[simp]
theorem objIso_hom
    {K : ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)}
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
    (h_compute : Functor.LeftDerived.ComputesAt
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY)) K) :
    (objIso f h_compute).hom =
      ((modulePullbackToDerived.{w} f).totalLeftDerivedCounit
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
        (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))).app K := sorry

end modulePullbackDerived.KFlat

namespace modulePullbackDerived.BoundedAbove

/-- A bounded-above homotopy complex with flat terms is a computation object for the total left
derived module pullback. -/
@[stacks 06YY "bounded-above computation of derived pullback"]
theorem computesAt
    {K : ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)}
    (hFlat : HomologicalComplex.IsTermwiseFlat K.as)
    (hbounded : CochainComplex.minus
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) K.as) :
    Functor.LeftDerived.ComputesAt
      (modulePullbackToDerived.{w} f)
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY)) K := sorry

end modulePullbackDerived.BoundedAbove
end RingedSite.Hom
