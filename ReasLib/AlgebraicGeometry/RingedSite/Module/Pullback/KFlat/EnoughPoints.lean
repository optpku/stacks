/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Stalk
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of K-flat complexes from enough points

If the source site has enough points, module pullback preserves K-flatness without a termwise
flatness hypothesis. The stalkwise argument is encapsulated here rather than exposed in the
public statement.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePullbackComplex

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [GrothendieckTopology.HasEnoughPoints.{w} JX]

/-- For a morphism presented by a morphism of commutative ringed sites, enough points on the
source imply that module pullback preserves K-flat cochain complexes.  The presentation-free
`0DEP` theorem for arbitrary morphisms of ringed topoi belongs to `RingedSite.ToposHom`. -/
theorem isKFlat_of_hasEnoughPoints
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY))
    [(f.modulePushforward.{w}).IsRightAdjoint]
    {K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ}
    (hK : K.IsKFlat) :
    ((f.modulePullbackComplex.{w}).obj K).IsKFlat := sorry

end RingedSite.Hom.modulePullbackComplex
