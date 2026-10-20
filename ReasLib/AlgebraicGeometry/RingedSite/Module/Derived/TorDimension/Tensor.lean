/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatRepresentative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and Tor-amplitude

This file owns tensor-product closure for flat representatives and Tor-amplitude on the derived
category of modules over a commutative ringed site.  The statement is specialized at precisely
the point where tensor products of flat module sheaves are used.
-/

@[expose] public section

-- Keep the existing standard derived-category model available in this leaf.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

open CategoryTheory
open RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/-- Tensoring interval-supported flat representatives adds their support intervals. -/
theorem HasFlatRepresentativeIn.tensor
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b c d : ℤ}
    (hK : HasFlatRepresentativeIn K a b) (hL : HasFlatRepresentativeIn L c d) :
    HasFlatRepresentativeIn (K ⊗ᴸ L) (a + c) (b + d) := sorry

/-- Lemma 21.46.7: Tor-amplitude intervals add under the canonical derived tensor product. -/
@[stacks 09JA]
theorem HasTorAmplitudeIn.tensor
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b c d : ℤ}
    (hK : HasTorAmplitudeIn K a b) (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗ᴸ L) (a + c) (b + d) := sorry

/-- The canonical derived tensor product of two objects of finite Tor dimension again has finite
Tor dimension. -/
theorem HasFiniteTorDimension.tensor
    {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : HasFiniteTorDimension K) (hL : HasFiniteTorDimension L) :
    HasFiniteTorDimension (K ⊗ᴸ L) := sorry

end

end RingedSite.Hom.ModuleDerived
