/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatRepresentative.LowerBounded
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback-stable flat representatives

A lower Tor-amplitude bound admits one K-flat representative with flat terms whose degreewise
pullback remains K-flat and termwise flat along every canonical commutative ringed-site
morphism in the target universes.
-/

@[expose] public section

open CategoryTheory
open RingedSite.Hom

noncomputable section

universe u v u' v' w

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}}
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 21.46.4, moreover clause: a lower Tor-amplitude representative can be chosen once so
that all canonical module pullbacks remain K-flat and termwise flat. -/
@[stacks 0F1M "moreover"]
theorem HasTorAmplitudeGE.exists_pullbackStableFlatRepresentative
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a : ℤ}
    (hE : HasTorAmplitudeGE E a) :
    ∃ (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) ℤ)
        (_ : E ≅ DerivedCategory.Q.obj K),
      K.IsStrictlyGE a ∧ K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K ∧
        ∀ {D : Type u'} [Category.{v'} D] {J' : GrothendieckTopology D}
          [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
          [HasWeakSheafify J' AddCommGrpCat.{w}]
          [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
          {O' : Sheaf J' CommRingCat.{w}}
          (f : RingedSite.Hom (RingedSite.ofCommRingSheaf J' O')
            (RingedSite.ofCommRingSheaf J O))
          [(f.modulePushforward.{w}).IsRightAdjoint],
          ((modulePullbackComplex f).obj K).IsKFlat ∧
            HomologicalComplex.IsTermwiseFlat ((modulePullbackComplex f).obj K) := sorry

end RingedSite.Hom.ModuleDerived
