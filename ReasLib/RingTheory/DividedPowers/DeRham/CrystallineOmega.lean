/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.QuotientSystem
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem.Limits
import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The p-adic completion of the relative divided-power differential module
attached to a ring homomorphism and divided powers on an ideal. -/
noncomputable abbrev crystallineOmegaD
    {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)] : Type v :=
  AdicCompletion (Ideal.span {(p : D)})
    (KaehlerDifferential.DeRham.dividedPowerDifferential f γbar)

/-- The relative divided-power derivation followed by the canonical map into
the p-adic completion of its differential module. -/
noncomputable def crystallineOmegaD_derivation
    {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)] :
    -- Local instance justification (instance diamond): f.toAlgebra selects the scalar action of the explicit ring map in the relative Derivation type.
    letI : Algebra A D := f.toAlgebra
    Derivation A D (crystallineOmegaD f γbar p) :=
  -- Local instance justification (instance diamond): f.toAlgebra fixes the same ring-map-selected scalar action for composing the relative derivation with completion.
  letI : Algebra A D := f.toAlgebra
  (AdicCompletion.of (Ideal.span {(p : D)})
    (KaehlerDifferential.DeRham.dividedPowerDifferential f γbar)).compDer
      (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation f γbar)

/-- The completed divided-power derivation sends each element to the canonical
completion image of its universal divided-power differential. -/
theorem crystallineOmegaD_derivation_apply
    {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)] (b : D) :
    -- Local instance justification (instance diamond): f.toAlgebra fixes the explicit ring-map-selected scalar action in the derivation and its elementwise formula.
    letI : Algebra A D := f.toAlgebra
    crystallineOmegaD_derivation f γbar p b =
      AdicCompletion.of (Ideal.span {(p : D)})
        (KaehlerDifferential.DeRham.dividedPowerDifferential f γbar)
        (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation f γbar b) := sorry

/-- The completed relative divided-power differential module is canonically
isomorphic to the inverse limit of its positive p-power quotients. -/
noncomputable def crystallineOmegaD_limitIso
    {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ModuleCat.of D (crystallineOmegaD f γbar p) ≅
      limit (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
        (KaehlerDifferential.DeRham.dividedPowerDifferential f γbar)) :=
  (AdicCompletion.positiveQuotientLimitIso (Ideal.span {(p : D)})
    (KaehlerDifferential.DeRham.dividedPowerDifferential f γbar)).symm

namespace CrystallineOmega

open KaehlerDifferential.DeRham

/-- The functor on positive inverse-system indices that removes the first `2 * n` stages. -/
private def stageShift (n : ℕ) : OrderDual ℕ+ ⥤ OrderDual ℕ+ :=
  (OrderHom.dual
    (⟨stageOffset n, fun _ _ hij ↦ Nat.add_le_add_right hij (2 * n)⟩ : ℕ+ →o ℕ+)).toFunctor

variable {A : Type u} [CommRing A] {D : Type v} [CommRing D]
variable (f : A →+* D) {J : Ideal D} (γ : DividedPowers J) (p n : ℕ)

/-- The positive quotient-module inverse system restricted to the tail starting after `2 * n`. -/
def shiftedPositiveQuotientSystem : PNatInverseSystem (ModuleCat.{v} D) :=
  stageShift n ⋙ AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
    (dividedPowerDifferential f γ)

/-- The explicit stage comparisons commute with the inverse-system transition maps. -/
private theorem actualSystemIso_naturality
    (hpow : Ideal.span {(p : D)} ^ n ≤ J)
    (i j : OrderDual ℕ+) (arrow : i ⟶ j) :
    (actualSystem f γ p n hpow).map arrow ≫
        (actualStageComparison f γ p n hpow (OrderDual.ofDual j)).hom =
      (actualStageComparison f γ p n hpow (OrderDual.ofDual i)).hom ≫
        (shiftedPositiveQuotientSystem f γ p n).map arrow := sorry

/-- The stable quotient-ring differential system is naturally isomorphic to the matching quotient-module tail. -/
def actualSystemIso (hpow : Ideal.span {(p : D)} ^ n ≤ J) :
    actualSystem f γ p n hpow ≅ shiftedPositiveQuotientSystem f γ p n :=
  NatIso.ofComponents
    (fun index ↦ actualStageComparison f γ p n hpow (OrderDual.ofDual index))
    (fun {i j} arrow ↦ actualSystemIso_naturality f γ p n hpow i j arrow)

/-- Tail-limit projections followed by power-quotient transitions form a compatible cone on the full tower. -/
private theorem tailCone_naturality (i j : OrderDual ℕ+) (arrow : i ⟶ j) :
    𝟙 (limit (shiftedPositiveQuotientSystem f γ p n)) ≫
        (limit.π (shiftedPositiveQuotientSystem f γ p n) j ≫
          ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {(p : D)})
            (dividedPowerDifferential f γ)
            (Nat.le_add_right ((OrderDual.ofDual j : ℕ+) : ℕ) (2 * n)))) =
      (limit.π (shiftedPositiveQuotientSystem f γ p n) i ≫
        ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {(p : D)})
          (dividedPowerDifferential f γ)
          (Nat.le_add_right ((OrderDual.ofDual i : ℕ+) : ℕ) (2 * n)))) ≫
        (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
          (dividedPowerDifferential f γ)).map arrow := sorry

/-- The cone on the full quotient-module tower with vertex the limit of its shifted tail. -/
private def tailCone :
    Cone (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
      (dividedPowerDifferential f γ)) where
  pt := limit (shiftedPositiveQuotientSystem f γ p n)
  π :=
    { app := fun index ↦
        limit.π (shiftedPositiveQuotientSystem f γ p n) index ≫
          ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {(p : D)})
            (dividedPowerDifferential f γ)
            (Nat.le_add_right ((OrderDual.ofDual index : ℕ+) : ℕ) (2 * n)))
      naturality := fun {i j} arrow ↦ tailCone_naturality f γ p n i j arrow }

/-- The map from a quotient-module tail limit to the full limit induced by its extension cone. -/
private def tailToFull :
    limit (shiftedPositiveQuotientSystem f γ p n) ⟶
      limit (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ)) :=
  limit.lift (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
    (dividedPowerDifferential f γ)) (tailCone f γ p n)

/-- The map from the full quotient-module limit to its tail limit induced by restricting the limit cone. -/
private def fullToTail :
    limit (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
      (dividedPowerDifferential f γ)) ⟶ limit (shiftedPositiveQuotientSystem f γ p n) :=
  limit.lift (shiftedPositiveQuotientSystem f γ p n)
    (Cone.whisker (stageShift n)
      (limit.cone (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ))))

/-- Extending a compatible tail and then restricting it is the identity on the tail limit. -/
private theorem cofinalTailLimitIso_hom_inv_id :
    tailToFull f γ p n ≫ fullToTail f γ p n =
      𝟙 (limit (shiftedPositiveQuotientSystem f γ p n)) := sorry

/-- Restricting a compatible full tower and then extending it is the identity on the full limit. -/
private theorem cofinalTailLimitIso_inv_hom_id :
    fullToTail f γ p n ≫ tailToFull f γ p n =
      𝟙 (limit (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ))) := sorry

/-- Removing a finite initial segment of the positive quotient tower preserves its inverse limit. -/
def cofinalTailLimitIso :
    limit (shiftedPositiveQuotientSystem f γ p n) ≅
      limit (AdicCompletion.positiveQuotientSystem (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ)) where
  hom := tailToFull f γ p n
  inv := fullToTail f γ p n
  hom_inv_id := cofinalTailLimitIso_hom_inv_id f γ p n
  inv_hom_id := cofinalTailLimitIso_inv_hom_id f γ p n

end CrystallineOmega

/-- Over a p-local base, the completed divided-power differential module is canonically
isomorphic to the inverse limit of stable quotient-ring differential modules when p is nilpotent modulo the divided-power ideal. -/
def crystallineOmegaD_actualLimitIso
    {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)] [Algebra (Int.LocalizationAtPrime p) A]
    (n : ℕ) (hpow : Ideal.span {(p : D)} ^ n ≤ J) :
    ModuleCat.of D (crystallineOmegaD f γbar p) ≅
      limit (CrystallineOmega.actualSystem f γbar p n hpow) :=
  crystallineOmegaD_limitIso f γbar p ≪≫
    (CrystallineOmega.cofinalTailLimitIso f γbar p n).symm ≪≫
    (HasLimit.isoOfNatIso (CrystallineOmega.actualSystemIso f γbar p n hpow)).symm
