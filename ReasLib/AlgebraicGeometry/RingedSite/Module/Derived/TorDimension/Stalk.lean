/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Stalk
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.CategoryTheory.Sites.Point.Enough
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalkwise detection of Tor-amplitude

Tor-amplitude is preserved by every derived module stalk and is detected by any conservative
indexed family of site points.  The enough-points result is the canonical specialization.
-/

@[expose] public section

-- Plain-ring stalk tensoring must retain the actual caller derivability input.

-- Infer the existing canonical tensor model for this commutative presentation.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

open CategoryTheory
open CategoryTheory.ObjectProperty
open RingedSite.Hom

noncomputable section

universe u v w t

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/-- Lemma 21.46.10 (1): a derived module's Tor-amplitude interval is preserved by
the derived stalk functor at every site point. -/
@[stacks 0DJJ "(1)"]
theorem HasTorAmplitudeIn.stalk
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b : ℤ}
    (hE : RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn
      (O := O) E a b)
    (p : GrothendieckTopology.Point.{w} J)
    [DerivedCategory.DerivedTensor.Right.Has (C := _root_.ModuleCat.{w} (p.stalkCommRing O))] :
    DerivedCategory.DerivedTensor.HasTorAmplitudeIn
      ((p.moduleStalkDerived O).obj E) a b := sorry

/-- Tor-amplitude is detected by any conservative indexed family of derived module stalks. -/
@[stacks 0DJJ "conservative family"]
theorem hasTorAmplitudeIn_iff_forall_stalk_of_isConservativeFamily
    {ι : Type t} (points : ι → GrothendieckTopology.Point.{w} J)
    [∀ i : ι, DerivedCategory.DerivedTensor.Right.Has
      (C := _root_.ModuleCat.{w} ((points i).stalkCommRing O))]
    (hpoints : (ofObj points).IsConservativeFamilyOfPoints)
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ) :
    RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn
      (O := O) E a b ↔
      ∀ i : ι, DerivedCategory.DerivedTensor.HasTorAmplitudeIn
        (((points i).moduleStalkDerived O).obj E) a b := sorry

/-- Lemma 21.46.10 (2): on a site with enough points, Tor-amplitude is equivalent to
Tor-amplitude of every derived point stalk. -/
@[stacks 0DJJ "(2)"]
theorem hasTorAmplitudeIn_iff_forall_stalk_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{w} J]
    [∀ p : GrothendieckTopology.Point.{w} J, DerivedCategory.DerivedTensor.Right.Has
      (C := _root_.ModuleCat.{w} (p.stalkCommRing O))]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ) :
    RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn
      (O := O) E a b ↔
      ∀ p : GrothendieckTopology.Point.{w} J,
        DerivedCategory.DerivedTensor.HasTorAmplitudeIn
          ((p.moduleStalkDerived O).obj E) a b := sorry

end RingedSite.Hom.ModuleDerived
