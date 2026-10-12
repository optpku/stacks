/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated derived pullback on ringed sites

The homotopy-level module pullback is triangulated, and the canonical localization is a
triangulated localization.  The generic total-derived API therefore equips unbounded derived
module pullback with its canonical shift comparison and exactness.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePullbackDerived

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

/-- Unbounded derived module pullback carries the canonical comparison with integer shifts. -/
@[stacks 06YY "exact derived pullback"]
noncomputable instance commShift :
    (modulePullbackDerived.{w} f).CommShift ℤ := inferInstance

/-- Lemma 21.18.2: unbounded derived module pullback is an exact functor of triangulated
categories. -/
@[stacks 06YY "exact derived pullback", instance]
theorem isTriangulated :
    (modulePullbackDerived.{w} f).IsTriangulated := sorry

end RingedSite.Hom.modulePullbackDerived
