/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import ReasLib.RingTheory.DividedPowers.AdicCompletion
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory KaehlerDifferential.DeRham

universe u v

namespace CrystallineOmega

/-- The positive index obtained by removing an initial segment of length `2 * n`. -/
def stageOffset (n : ℕ) (e : ℕ+) : ℕ+ :=
  ⟨(e : ℕ) + 2 * n, Nat.lt_of_lt_of_le e.pos (Nat.le_add_right (e : ℕ) (2 * n))⟩

variable {A : Type u} [CommRing A] {D : Type v} [CommRing D]
variable (f : A →+* D) {J : Ideal D} (γ : DividedPowers J) (p n : ℕ)
variable (hpow : Ideal.span {(p : D)} ^ n ≤ J)

/-- The principal ideal power at a shifted positive stage. -/
private abbrev stageIdeal (e : ℕ+) : Ideal D :=
  Ideal.span {(p : D)} ^ ((stageOffset n e : ℕ+) : ℕ)

/-- The quotient ring homomorphism at a shifted positive stage. -/
private abbrev stageQuotient (e : ℕ+) : D →+* D ⧸ stageIdeal p n e :=
  Ideal.Quotient.mk (stageIdeal p n e)

/-- The divided powers induced on the image ideal in a stable quotient ring. -/
private def stageDividedPowers (e : ℕ+) : DividedPowers (J.map (stageQuotient p n e)) :=
  DividedPowers.Quotient.dividedPowers γ
    (DividedPowers.isStableUnderPowers_principal γ (p : D) n hpow (e : ℕ))

/-- The relative divided-power differential module of the stable quotient ring,
with its scalar action restricted to the original ring. -/
def actualStage (e : ℕ+) : ModuleCat.{v} D :=
  (ModuleCat.restrictScalars (stageQuotient p n e)).obj
    (ModuleCat.of (D ⧸ stageIdeal p n e)
      (dividedPowerDifferential ((stageQuotient p n e).comp f)
        (stageDividedPowers γ p n hpow e)))

/-- The map on Kähler differentials followed by the divided-power quotient projection. -/
private def forwardKaehlerMap (e : ℕ+) :
    -- Local instance justification (defeq pin): the Kähler source must use the algebra action in dividedPowerDifferential f γ.
    letI : Algebra A D := f.toAlgebra
    KaehlerDifferential A D →ₗ[D] actualStage f γ p n hpow e :=
  -- Local instance justification (defeq pin): the Kähler map must use the algebra action in dividedPowerDifferential f γ.
  letI : Algebra A D := f.toAlgebra
  -- Local instance justification (defeq pin): the target projection uses the composite ring homomorphism's algebra in dividedPowerDifferential.
  letI : Algebra A (D ⧸ stageIdeal p n e) := ((stageQuotient p n e).comp f).toAlgebra
  ((dividedPowerRelations ((stageQuotient p n e).comp f)
      (stageDividedPowers γ p n hpow e)).mkQ.restrictScalars D).comp
    (KaehlerDifferential.map A A D (D ⧸ stageIdeal p n e))

/-- The quotient-ring differential map annihilates the original divided-power relations. -/
private theorem forwardRelations (e : ℕ+) :
    -- Local instance justification (defeq pin): the relation submodule and the Kähler map use f.toAlgebra.
    letI : Algebra A D := f.toAlgebra
    dividedPowerRelations f γ ≤ LinearMap.ker (forwardKaehlerMap f γ p n hpow e) := sorry

/-- The induced map from divided-power differentials to a stable quotient-ring stage. -/
private def stageDifferentialMap (e : ℕ+) :
    dividedPowerDifferential f γ →ₗ[D] actualStage f γ p n hpow e :=
  -- Local instance justification (defeq pin): the quotient descent uses the Kähler module underlying dividedPowerDifferential f γ.
  letI : Algebra A D := f.toAlgebra
  (dividedPowerRelations f γ).liftQ (forwardKaehlerMap f γ p n hpow e)
    (forwardRelations f γ p n hpow e)

/-- The stable quotient-ring differential map annihilates the corresponding ideal multiple. -/
private theorem forwardPower (e : ℕ+) :
    stageIdeal (D := D) p n e • (⊤ : Submodule D (dividedPowerDifferential f γ)) ≤
      LinearMap.ker (stageDifferentialMap f γ p n hpow e) := sorry

/-- The explicit map from a power quotient of differentials to quotient-ring differentials. -/
def actualStageComparisonInv (e : ℕ+) :
    AdicCompletion.positiveQuotientStage (Ideal.span {(p : D)})
      (dividedPowerDifferential f γ) (stageOffset n e) →ₗ[D]
        actualStage f γ p n hpow e :=
  (stageIdeal p n e • (⊤ : Submodule D (dividedPowerDifferential f γ))).liftQ
    (stageDifferentialMap f γ p n hpow e) (forwardPower f γ p n hpow e)

/-- Projected divided-power differentials agree on representatives of the same quotient class. -/
private theorem quotientDerivation_wellDefined (e : ℕ+) (left right : D)
    (hrel : (stageIdeal (D := D) p n e).quotientRel left right) :
    (stageIdeal (D := D) p n e • (⊤ : Submodule D (dividedPowerDifferential f γ))).mkQ
        (dividedPowerDifferentialDerivation f γ left) =
      (stageIdeal p n e • (⊤ : Submodule D (dividedPowerDifferential f γ))).mkQ
        (dividedPowerDifferentialDerivation f γ right) := sorry

/-- The projected differential function on the quotient ring, defined by quotient descent. -/
private def quotientDerivationFn (e : ℕ+) (value : D ⧸ stageIdeal p n e) :
    AdicCompletion.positiveQuotientStage (Ideal.span {(p : D)})
      (dividedPowerDifferential f γ) (stageOffset n e) :=
  Quotient.liftOn value
    (fun representative ↦
      (stageIdeal p n e • (⊤ : Submodule D (dividedPowerDifferential f γ))).mkQ
        (dividedPowerDifferentialDerivation f γ representative))
    (quotientDerivation_wellDefined f γ p n e)

/-- The descended differential function is additive. -/
private theorem quotientDerivation_add (e : ℕ+) (left right : D ⧸ stageIdeal p n e) :
    quotientDerivationFn f γ p n e (left + right) =
      quotientDerivationFn f γ p n e left + quotientDerivationFn f γ p n e right := sorry

/-- The descended differential function respects scalars from the base ring. -/
private theorem quotientDerivation_smul (e : ℕ+) (scalar : A)
    (value : D ⧸ stageIdeal p n e) :
    -- Local instance justification (defeq pin): base scalars must act through the specified ring map f.
    letI : Algebra A D := f.toAlgebra
    -- Local instance justification (defeq pin): the quotient-ring scalar action must match the ring-hom-based target differential module.
    letI : Algebra A (D ⧸ stageIdeal p n e) := ((stageQuotient p n e).comp f).toAlgebra
    quotientDerivationFn f γ p n e (scalar • value) =
      scalar • quotientDerivationFn f γ p n e value := sorry

/-- The descended differential function vanishes at one. -/
private theorem quotientDerivation_one (e : ℕ+) :
    quotientDerivationFn f γ p n e 1 = 0 := sorry

/-- The descended differential function satisfies the Leibniz rule for the canonical quotient action. -/
private theorem quotientDerivation_leibniz (e : ℕ+) (left right : D ⧸ stageIdeal p n e) :
    quotientDerivationFn f γ p n e (left * right) =
      left • quotientDerivationFn f γ p n e right +
        right • quotientDerivationFn f γ p n e left := sorry

/-- The module-valued derivation on the quotient ring obtained by projecting original differentials. -/
private def quotientDerivation (e : ℕ+) :
    -- Local instance justification (defeq pin): the quotient derivation uses the base algebra induced by f.
    letI : Algebra A D := f.toAlgebra
    -- Local instance justification (defeq pin): the quotient derivation must use the algebra in the target differential owner.
    letI : Algebra A (D ⧸ stageIdeal p n e) := ((stageQuotient p n e).comp f).toAlgebra
    Derivation A (D ⧸ stageIdeal p n e)
      (AdicCompletion.positiveQuotientStage (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ) (stageOffset n e)) :=
  -- Local instance justification (defeq pin): the quotient derivation uses the base algebra induced by f.
  letI : Algebra A D := f.toAlgebra
  -- Local instance justification (defeq pin): the quotient derivation must use the algebra in the target differential owner.
  letI : Algebra A (D ⧸ stageIdeal p n e) := ((stageQuotient p n e).comp f).toAlgebra
  {
  toFun := quotientDerivationFn f γ p n e
  map_add' := quotientDerivation_add f γ p n e
  map_smul' := quotientDerivation_smul f γ p n e
  map_one_eq_zero' := quotientDerivation_one f γ p n e
  leibniz' := quotientDerivation_leibniz f γ p n e }

/-- The descended quotient derivation annihilates the quotient divided-power relations. -/
private theorem inverseRelations (e : ℕ+) :
    -- Local instance justification (defeq pin): lifting the quotient derivation uses the algebra induced by f.
    letI : Algebra A D := f.toAlgebra
    -- Local instance justification (defeq pin): the quotient Kähler module must use the algebra in the divided-power differential owner.
    letI : Algebra A (D ⧸ stageIdeal p n e) := ((stageQuotient p n e).comp f).toAlgebra
    dividedPowerRelations ((stageQuotient p n e).comp f)
        (stageDividedPowers γ p n hpow e) ≤
      LinearMap.ker (quotientDerivation f γ p n e).liftKaehlerDifferential := sorry

/-- The explicit map from quotient-ring differentials to a power quotient of original differentials. -/
def actualStageComparisonHom (e : ℕ+) :
    actualStage f γ p n hpow e →ₗ[D]
      AdicCompletion.positiveQuotientStage (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ) (stageOffset n e) :=
  -- Local instance justification (defeq pin): the lifted quotient derivation uses the base algebra induced by f.
  letI : Algebra A D := f.toAlgebra
  -- Local instance justification (defeq pin): the quotient Kähler module must use the algebra in the divided-power differential owner.
  letI : Algebra A (D ⧸ stageIdeal p n e) := ((stageQuotient p n e).comp f).toAlgebra
  ((dividedPowerRelations ((stageQuotient p n e).comp f)
      (stageDividedPowers γ p n hpow e)).liftQ
    (quotientDerivation f γ p n e).liftKaehlerDifferential
    (inverseRelations f γ p n hpow e)).restrictScalars D

/-- Composing the stage comparison with its explicit inverse is the identity on the actual stage. -/
private theorem actualStageComparison_hom_inv_id (e : ℕ+) :
    (actualStageComparisonInv f γ p n hpow e).comp
        (actualStageComparisonHom f γ p n hpow e) = LinearMap.id := sorry

/-- Composing the inverse stage comparison with the comparison is the identity on the quotient stage. -/
private theorem actualStageComparison_inv_hom_id (e : ℕ+) :
    (actualStageComparisonHom f γ p n hpow e).comp
        (actualStageComparisonInv f γ p n hpow e) = LinearMap.id := sorry

/-- Stable quotient-ring divided-power differentials are canonically isomorphic to the matching power quotient. -/
def actualStageComparison (e : ℕ+) :
    actualStage f γ p n hpow e ≅
      AdicCompletion.positiveQuotientStage (Ideal.span {(p : D)})
        (dividedPowerDifferential f γ) (stageOffset n e) where
  hom := ModuleCat.ofHom (actualStageComparisonHom f γ p n hpow e)
  inv := ModuleCat.ofHom (actualStageComparisonInv f γ p n hpow e)
  hom_inv_id := congrArg ModuleCat.ofHom (actualStageComparison_hom_inv_id f γ p n hpow e)
  inv_hom_id := congrArg ModuleCat.ofHom (actualStageComparison_inv_hom_id f γ p n hpow e)

/-- The stage comparison sends the differential of a quotient representative to the projected original differential. -/
theorem actualStageComparison_hom_d (e : ℕ+) (value : D) :
    (actualStageComparison f γ p n hpow e).hom
        (dividedPowerDifferentialDerivation ((stageQuotient p n e).comp f)
          (stageDividedPowers γ p n hpow e) (stageQuotient p n e value)) =
      (stageIdeal p n e • (⊤ : Submodule D (dividedPowerDifferential f γ))).mkQ
        (dividedPowerDifferentialDerivation f γ value) := sorry

/-- The inverse stage comparison sends a projected original differential to the quotient-ring differential. -/
theorem actualStageComparison_inv_mk_d (e : ℕ+) (value : D) :
    (actualStageComparison f γ p n hpow e).inv
        ((stageIdeal p n e • (⊤ : Submodule D (dividedPowerDifferential f γ))).mkQ
          (dividedPowerDifferentialDerivation f γ value)) =
      dividedPowerDifferentialDerivation ((stageQuotient p n e).comp f)
        (stageDividedPowers γ p n hpow e) (stageQuotient p n e value) := sorry

/-- The transition between actual stages obtained by transporting the canonical quotient-module transition. -/
def actualStageMap {i j : ℕ+} (hij : i ≤ j) :
    actualStage f γ p n hpow j ⟶ actualStage f γ p n hpow i :=
  (actualStageComparison f γ p n hpow j).hom ≫
    ModuleCat.ofHom (AdicCompletion.transitionMap (Ideal.span {(p : D)})
      (dividedPowerDifferential f γ) (Nat.add_le_add_right hij (2 * n))) ≫
    (actualStageComparison f γ p n hpow i).inv

/-- Actual stage transitions send quotient-ring differentials to the corresponding differentials at the smaller stage. -/
theorem actualStageMap_d {i j : ℕ+} (hij : i ≤ j) (value : D) :
    actualStageMap f γ p n hpow hij
        (dividedPowerDifferentialDerivation ((stageQuotient p n j).comp f)
          (stageDividedPowers γ p n hpow j) (stageQuotient p n j value)) =
      dividedPowerDifferentialDerivation ((stageQuotient p n i).comp f)
        (stageDividedPowers γ p n hpow i) (stageQuotient p n i value) := sorry

/-- The transported actual-stage transition at equal indices is the identity. -/
private theorem actualSystem_map_id (e : ℕ+) :
    actualStageMap f γ p n hpow (le_refl e) = 𝟙 (actualStage f γ p n hpow e) := sorry

/-- Transported actual-stage transitions compose along inequalities. -/
private theorem actualSystem_map_comp {i j k : ℕ+} (hij : i ≤ j) (hjk : j ≤ k) :
    actualStageMap f γ p n hpow (hij.trans hjk) =
      actualStageMap f γ p n hpow hjk ≫ actualStageMap f γ p n hpow hij := sorry

/-- The positive inverse system of actual quotient-ring divided-power differential modules on a stable tail. -/
def actualSystem : PNatInverseSystem (ModuleCat.{v} D) where
  obj index := actualStage f γ p n hpow (OrderDual.ofDual index)
  map arrow := actualStageMap f γ p n hpow (leOfHom arrow)
  map_id index := actualSystem_map_id f γ p n hpow (OrderDual.ofDual index)
  map_comp first second := actualSystem_map_comp f γ p n hpow (leOfHom second) (leOfHom first)

end CrystallineOmega
