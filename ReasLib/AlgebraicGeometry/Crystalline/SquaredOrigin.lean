/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.RingTheory.DividedPowers.SquaredOrigin.Envelope
public import ReasLib.AlgebraicGeometry.DividedPowers.Affine
public import ReasLib.AlgebraicGeometry.Crystalline.RingedMorphism
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Geometry
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.GlobalSections

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DividedPowers Opposite
open AlgebraicGeometry.Scheme.Crystalline

namespace Crystalline.SquaredOrigin

/-- The spectrum of the ring of `p`-adic integers. -/
abbrev baseScheme (p : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of ℤ_[p])

/-- The affine scheme defined by the square of the origin ideal in two variables. -/
abbrev affineScheme (p : ℕ) [Fact p.Prime] : Scheme.{0} :=
  Spec (CommRingCat.of (coordinateRing p))

/-- The prime-local structure morphism of the spectrum of the `p`-adic integers. -/
def baseStructure (p : ℕ) [Fact p.Prime] :
    baseScheme p ⟶ Spec (CommRingCat.of (ULift.{0} (Int.LocalizationAtPrime p))) :=
  Spec.map (CommRingCat.ofHom ((PadicInt.fromLocalization p).comp
    (ULift.ringEquiv : ULift.{0} (Int.LocalizationAtPrime p) ≃+* Int.LocalizationAtPrime p).toRingHom))

/-- The affine ideal sheaf of the prime ideal is quasi-coherent. -/
theorem baseIdeal_quasiCoherent (p : ℕ) [Fact p.Prime] :
    (DividedPowers.affineIdeal (I := padicIdeal p)).toModule.IsQuasicoherent := sorry

/-- The coefficient morphism from the squared origin annihilates the prime ideal sheaf. -/
theorem sourceToClosed_factorCondition (p : ℕ) [Fact p.Prime] :
    DividedPowers.affineIdeal (I := padicIdeal p) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] (coordinateRing p)))).ker := sorry

/-- The coefficient morphism factored through the closed fibre of the prime ideal. -/
def sourceToClosed (p : ℕ) [Fact p.Prime] :
    affineScheme p ⟶ (DividedPowers.affineIdeal (I := padicIdeal p)).subscheme :=
  (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] (coordinateRing p)))).toImage ≫
    Scheme.IdealSheafData.inclusion (sourceToClosed_factorCondition p)

/-- The closed-fibre factorization recovers the coefficient morphism. -/
theorem sourceToClosed_comp (p : ℕ) [Fact p.Prime] :
    sourceToClosed p ≫ (DividedPowers.affineIdeal (I := padicIdeal p)).subschemeι =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] (coordinateRing p))) := sorry

/-- The prime is nilpotent on every affine open of the squared origin. -/
theorem affine_p_nilpotent (p : ℕ) [Fact p.Prime] (U : (affineScheme p).affineOpens) :
    IsNilpotent (p : Γ(affineScheme p, U)) := sorry

/-- The crystalline base of the squared origin over the canonical `p`-adic divided powers. -/
def canonicalBase (p : ℕ) [Fact p.Prime] : Base.{0} p :=
  Base.of p (baseScheme p) (DividedPowers.affineIdeal (I := padicIdeal p))
    (baseIdeal_quasiCoherent p) (DividedPowers.affine (PadicInt.dividedPowers p))
    (DividedPowers.affine_compatible (PadicInt.dividedPowers p))
    (baseStructure p) (affineScheme p) (sourceToClosed p) (affine_p_nilpotent p)

/-- Global affine sections of the canonical base recover the `p`-adic divided powers. -/
theorem canonicalBase_dividedPowersCompatible (p : ℕ) [Fact p.Prime] :
    IsDPMorphism (PadicInt.dividedPowers p)
      ((canonicalBase p).dividedPowers ⟨⊤, isAffineOpen_top (baseScheme p)⟩)
      (Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])).inv.hom := sorry

/-- The geometric Frobenius of the squared origin is the spectrum of its `p`th-power map. -/
def sourceFrobenius (p : ℕ) [Fact p.Prime] : affineScheme p ⟶ affineScheme p :=
  Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap (coordinateIdeal p) (frobenius (MvPolynomial Coord (ZMod p)) p)
      (fun a ha ↦ (coordinateIdeal p).pow_mem_of_mem ha p (Fact.out : p.Prime).pos)))

/-- Geometric Frobenius is compatible with the identity divided-power base morphism. -/
theorem sourceFrobenius_over (p : ℕ) [Fact p.Prime] :
    sourceFrobenius p ≫ (canonicalBase p).sourceToClosed =
      (canonicalBase p).sourceToClosed ≫
        (DividedPowerScheme.Hom.id (canonicalBase p).dividedPowerScheme).zeroFiberMap := sorry

/-- Degree-zero crystalline cohomology is the ring of global crystalline functions. -/
abbrev cohomology (p : ℕ) [Fact p.Prime] : RingCat.{1} :=
  RingedSite.Hom.globalSectionsRing (canonicalBase p).ringedSite

/-- Pullback of global crystalline functions by the actual geometric Frobenius. -/
def frobeniusOnCohomology (p : ℕ) [Fact p.Prime] : cohomology p ⟶ cohomology p :=
  (AlgebraicGeometry.Scheme.Crystalline.Ringed.morphism (canonicalBase p) (canonicalBase p)
    (DividedPowerScheme.Hom.id (canonicalBase p).dividedPowerScheme)
    (Category.id_comp _) (sourceFrobenius p) (sourceFrobenius_over p)).globalSectionsMap

/-- Evaluation of crystalline functions on a genuine completed-envelope stage, followed by
reduction to the requested principal-adic quotient. -/
def cohomologyStageEvaluation {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) (n : ℕ) :
    cohomology p →+* data.D ⧸ Ideal.span {(p : data.D)} ^ n :=
  let Z := data.completedObject
  let B := canonicalBase p
  let T := CechCrisCover.completedSmallStage (PadicInt.dividedPowers p)
    (coordinate_prime_bot p) (coordinate_p_nilpotent p) B.ideal B.dividedPowers B.compatible
    B.sourceToClosed (𝟙 (affineScheme p)) (sourceToClosed_comp p) rfl
    (canonicalBase_dividedPowersCompatible p)
    (AlgebraicGeometry.IsOpenImmersion.of_isIso (𝟙 (affineScheme p))) Z n
  let R := pAdicQuotientRing (PadicInt.dividedPowers p)
    (algebraMap ℤ_[p] (coordinateRing p)) (coordinate_prime_bot p)
    (coordinate_p_nilpotent p) Z n
  let evaluation := (limit.π B.ringedSite.structureSheaf.obj (op T)).hom
  let functions := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
    (ULift.ringEquiv : ULift.{1} Γ(Spec (CommRingCat.of R), ⊤) ≃+*
      Γ(Spec (CommRingCat.of R), ⊤)).toRingHom
  (Ideal.Quotient.factorPow (Ideal.span {(p : data.D)})
    (Nat.le_add_right n (pAdicOffset (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (coordinateRing p)) (coordinate_prime_bot p)
      (coordinate_p_nilpotent p) Z))).comp (functions.comp evaluation)

/-- Evaluation at crystalline quotient stages commutes with principal-power reduction. -/
theorem cohomologyStageEvaluation_compatible {p : ℕ} [Fact p.Prime]
    (data : EnvelopeData p) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : data.D)}) hle).comp
        (cohomologyStageEvaluation data n) = cohomologyStageEvaluation data m := sorry

/-- The comparison to the completed envelope is the limit of the actual stage evaluations. -/
def cohomologyToCompleted {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    cohomology p →+* data.D :=
  (@AdicCompletion.ofAlgEquiv data.D _ (Ideal.span {(p : data.D)})
    data.completedObject.complete).symm.toRingHom.comp
    (AdicCompletion.liftRingHom (Ideal.span {(p : data.D)})
      (cohomologyStageEvaluation data) (cohomologyStageEvaluation_compatible data))

/-- Global crystalline functions have zero completed relative differential. -/
theorem cohomologyToCompleted_closed {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (s : cohomology p) : cohomologyToCompleted data s ∈ closedForms data := sorry

/-- The additive comparison from crystalline functions to closed completed-envelope elements. -/
def cohomologyToClosedForms {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    cohomology p →+ closedForms data :=
  (cohomologyToCompleted data).toAddMonoidHom.codRestrict
    (closedForms data) (cohomologyToCompleted_closed data)

/-- Evaluation identifies crystalline global functions bijectively with closed elements. -/
theorem cohomologyToClosedForms_bijective {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    Function.Bijective (cohomologyToClosedForms data) := sorry

/-- The comparison intertwines geometric Frobenius pullback and completed polynomial Frobenius. -/
theorem cohomologyToClosedForms_frobenius {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (s : cohomology p) :
    cohomologyToClosedForms data (frobeniusOnCohomology p s) =
      frobeniusOnClosedForms data (cohomologyToClosedForms data s) := sorry

/-- Crystalline global functions on the squared origin contain nonzero `p`-torsion. -/
theorem cohomology_has_p_torsion (p : ℕ) [Fact p.Prime] :
    ∃ t : cohomology p, t ≠ 0 ∧ (p : ℤ) • t = 0 := sorry

/-- Geometric Frobenius pullback on crystalline global functions of the squared origin
is not injective. -/
theorem frobeniusPullback_not_injective (p : ℕ) [Fact p.Prime] :
    ¬ Function.Injective (frobeniusOnCohomology p) := sorry

end Crystalline.SquaredOrigin
