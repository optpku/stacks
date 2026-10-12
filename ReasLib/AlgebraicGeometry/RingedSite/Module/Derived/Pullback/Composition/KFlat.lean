/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Composition of derived pullbacks from K-flat models

For commutative site presentations, K-flat complexes with flat terms form a resolving class and
are preserved by module pullback.  Consequently the canonical comparison from iterated derived
pullback to derived pullback along the composite is invertible.  This is the site-presented form
of the ringed-topos composition theorem.
-/

open CategoryTheory

noncomputable section

universe uX vX uY vY uZ vZ w

namespace RingedSite.Hom.modulePullbackDerived

variable {C : Type uX} [Category.{vX} C]
variable {D : Type uY} [Category.{vY} D]
variable {E : Type uZ} [Category.{vZ} E]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
  {JZ : GrothendieckTopology E}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JZ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
  {OZ : Sheaf JZ CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JZ AddCommGrpCat.{w}]
variable [JZ.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
  [UnivLE.{max uZ vZ, w}]

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable (g : RingedSite.Hom (RingedSite.ofCommRingSheaf JY OY)
  (RingedSite.ofCommRingSheaf JZ OZ))
variable [(f.modulePushforward.{w}).IsRightAdjoint]
variable [(g.modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} f)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} g)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JZ OZ))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} (f.comp g))
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JZ OZ))]

/-- Lemma 21.18.3 (0D6D), site-presented commutative form: the canonical comparison from
iterated derived module pullback to derived pullback along the composite is invertible. -/
@[stacks 0D6D "site-presented commutative form"]
theorem compComparison_isIso : IsIso (compComparison f g) := sorry

end RingedSite.Hom.modulePullbackDerived

-- The `sorryAx` below is confined to the Prop-valued proof that the canonical comparison is
-- invertible. No inverse morphism is extracted from that placeholder proof in this stage.
