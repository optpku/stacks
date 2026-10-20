/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.FlatRepresentative
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Infer the existing canonical tensor model for this commutative presentation.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/-!
# Flat representatives and Tor-amplitude

This file packages interval-bounded and lower-bounded flat representative criteria.  The
Tor-amplitude bridges are stated for the canonical tensor product attached to a commutative ring
sheaf presentation; they do not accept unrelated monoidal structures on an arbitrary ringed site.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

section Predicate

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [MonoidalCategory (ModuleCat.{w} X)]

/-- The object property of admitting a termwise-flat module-sheaf representative supported in
`[a, b]`. -/
abbrev flatRepresentativeIn (a b : ℤ) : ObjectProperty (ModuleDerived.{w} X) :=
  DerivedCategory.flatRepresentativeIn (C := ModuleCat.{w} X) a b

/-- A derived module sheaf admits a termwise-flat representative supported in `[a, b]`. -/
abbrev HasFlatRepresentativeIn (E : ModuleDerived.{w} X) (a b : ℤ) : Prop :=
  flatRepresentativeIn (X := X) a b E

/-- The flat-representative predicate unfolds to a supported termwise-flat cochain
representative. -/
theorem hasFlatRepresentativeIn_iff (E : ModuleDerived.{w} X) (a b : ℤ) :
    HasFlatRepresentativeIn E a b ↔
      ∃ (K : CochainComplex (ModuleCat.{w} X) ℤ) (_ : E ≅ DerivedCategory.Q.obj K),
        K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ HomologicalComplex.IsTermwiseFlat K := sorry

end Predicate

section CanonicalTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/-- Lemma 21.46.3: Tor-amplitude in `[a, b]` is equivalent to admitting a termwise-flat
representative supported in `[a, b]`. -/
@[stacks 08G1]
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeIn
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔ HasFlatRepresentativeIn E a b := sorry

/-- A Tor-amplitude bound produces a termwise-flat representative in the same interval. -/
theorem HasTorAmplitudeIn.hasFlatRepresentativeIn
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    HasFlatRepresentativeIn E a b := sorry

/-- A termwise-flat representative supported in `[a, b]` gives Tor-amplitude in `[a, b]`. -/
theorem HasFlatRepresentativeIn.hasTorAmplitudeIn
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a b : ℤ}
    (hE : HasFlatRepresentativeIn E a b) :
    HasTorAmplitudeIn E a b := sorry

end CanonicalTensor

end RingedSite.Hom.ModuleDerived
