/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Point
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
import Mathlib.Tactic.CrossRefAttribute

/-!
# Points and stalk maps of commutative ringed sites

This file owns the image of a site point under a morphism of commutative ringed sites and the
induced map on commutative stalk rings.  These constructions are independent of module pullback.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf JC CommRingCat.{w}}
variable {O' : Sheaf JD CommRingCat.{w}}
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC O)
  (RingedSite.ofCommRingSheaf JD O'))
variable (p : GrothendieckTopology.Point.{w} JC)
variable [InitiallySmall (f.base ⋙ p.fiber).Elements]

/-- The image `f(p)` of a point under a morphism of commutative ringed sites, obtained by the
canonical comap along the contravariant base functor. -/
@[stacks 05V5 "image point"]
abbrev pointMap : GrothendieckTopology.Point.{w} JD :=
  p.comapOfMorphismOfSites (J := JD) f.base (hF := f.isMorphismOfSites)

variable [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]

/-- The coefficient-generic point-comap comparison specialized to commutative-ring-valued
sheaves. -/
noncomputable abbrev commRingFiberIso :
    (pointMap f p).sheafFiber ≅
      f.base.sheafPullback CommRingCat.{w} JD JC ⋙ p.sheafFiber :=
  p.sheafFiberComapIsoOfMorphismOfSites (J := JD) f.base CommRingCat
    (hF := f.isMorphismOfSites)

/-- The canonical map `O'_{f(p)} ⟶ O_p` on commutative stalk rings. -/
@[stacks 05V5 "stalk ring map"]
noncomputable abbrev stalkMap :
    (pointMap f p).stalkCommRing O' ⟶ p.stalkCommRing O :=
  (commRingFiberIso f p).hom.app O' ≫
    p.stalkCommRingMap (inverseImageStructureSheafMap f)

end RingedSite.Hom
