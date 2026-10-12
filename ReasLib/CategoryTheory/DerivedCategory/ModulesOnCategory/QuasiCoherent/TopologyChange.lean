/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Adjunction.Restriction.InverseImage
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticClosure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherent derived modules under a change from the chaotic topology

This leaf specializes inverse-image restriction of an adjunction to the canonical
quasi-coherence property on a chaotic ringed site.  The complex-level K-flat hypothesis in
Lemma 21.43.12 enters through the unit-isomorphism condition that it establishes.
-/

@[expose] public section

-- Keep these operations on the already specified canonical derived-category model.
-- Local instance justification (defeq pin): the ringed-site and commutative-ring-sheaf presentations below denote the same standard quotient; enable both existing reducible presentation owners so their Q objects share that model.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory

noncomputable section

-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

open CategoryTheory

universe u v w uD vD

namespace CategoryTheory.ModulesOnCategory.Chaotic.TopologyChange

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C)
  CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

variable {D : Type uD} [Category.{vD} D]
variable {epsilonPullback : DerivedCategory
    (SheafOfModules.RingedSite.ringedSiteModuleCategory.{
      u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) O) ⥤ D}
variable {rEpsilonPushforward : D ⥤ DerivedCategory
    (SheafOfModules.RingedSite.ringedSiteModuleCategory.{
      u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) O)}
variable (adj : epsilonPullback ⊣ rEpsilonPushforward)

/-- The target-side property of objects whose derived pushforward is canonically
quasi-coherent on the chaotic site. -/
@[stacks 0GZS "target inverse-image property"]
abbrev targetProperty : ObjectProperty D :=
  (isQuasiCoherent O).inverseImage rEpsilonPushforward

/-- The derived unit condition on canonical quasi-coherent objects supplied by the K-flat
sections comparison in Lemma 21.43.12. -/
@[stacks 0GZS "derived unit condition"]
abbrev UnitCondition : Prop := isQuasiCoherent O ≤ adj.unitIsoProperty

/-- The derived inverse-image functor restricted to canonical quasi-coherent objects. -/
@[stacks 0GZS "restricted derived inverse image"]
noncomputable abbrev pullbackRestriction (hunit : UnitCondition O adj) :
    QC O ⥤
      (targetProperty (rEpsilonPushforward := rEpsilonPushforward) O).FullSubcategory :=
  Adjunction.InverseImageRestriction.left adj (isQuasiCoherent O) hunit

/-- The derived pushforward restricted to objects satisfying `targetProperty O adj`. -/
@[stacks 0GZS "restricted derived pushforward"]
noncomputable abbrev pushforwardRestriction :
    (targetProperty (rEpsilonPushforward := rEpsilonPushforward) O).FullSubcategory ⥤
      QC O :=
  Adjunction.InverseImageRestriction.right
    (G := rEpsilonPushforward) (isQuasiCoherent O)

/-- The topology-change adjunction restricted to the two quasi-coherent object properties. -/
@[stacks 0GZS "restricted topology-change adjunction"]
noncomputable abbrev restrictedAdjunction (hunit : UnitCondition O adj) :
    pullbackRestriction O adj hunit ⊣
      pushforwardRestriction (rEpsilonPushforward := rEpsilonPushforward) O :=
  Adjunction.InverseImageRestriction.adjunction adj (isQuasiCoherent O) hunit

/-- Lemma 21.43.12 (0GZS), in the derived unit form supplied by its K-flat sections
hypothesis: the restricted `Rε_*` is an equivalence from the objects whose pushforward is in
`QC O` to `QC O`. -/
@[stacks 0GZS]
theorem pushforwardRestriction_isEquivalence_of_unitCondition
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hunit : UnitCondition O adj) :
    (pushforwardRestriction
      (rEpsilonPushforward := rEpsilonPushforward) O).IsEquivalence := sorry

/-- The restricted `ε^*` is the mutually quasi-inverse equivalence under the same unit
condition. -/
@[stacks 0GZS "inverse-image companion"]
theorem pullbackRestriction_isEquivalence_of_unitCondition
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hunit : UnitCondition O adj) :
    (pullbackRestriction O adj hunit).IsEquivalence := sorry

end CategoryTheory.ModulesOnCategory.Chaotic.TopologyChange
