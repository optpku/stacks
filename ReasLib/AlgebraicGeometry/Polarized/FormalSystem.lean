/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Sequential polarized towers over inverse limits of rings

A sequential inverse system of rings with surjective locally nilpotent
transitions, cartesian proper flat finite-presentation schemes over the
spectra, and compatible invertible modules with ample first stage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- A sequential inverse system of rings, cartesian schemes over the stage
spectra, and compatible invertible modules, with ampleness only at stage `0`. -/
structure FormalSystem : Type (u + 1) where
  /-- Sequential inverse system `(R_n)` of commutative rings. -/
  ringSystem : SequentialInverseSystem CommRingCat.{u}
  /-- Chosen limiting cone, so the vertex is `R = lim R_n`. -/
  limitCone : LimitCone ringSystem
  /-- Successor transition maps of `(R_n)` are surjective. -/
  ringMapsSurjective : ringSystem.Surjective
  /-- Kernels of successor transition maps are locally nilpotent. -/
  kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent
  /-- Stage schemes `X n`. -/
  X : ℕ → Scheme.{u}
  /-- Structure morphisms `X n ⟶ Spec (R_n)`. -/
  hom : ∀ n, X n ⟶ Spec (ringSystem.family n)
  /-- Successor morphisms `i_n : X n ⟶ X (n + 1)`. -/
  step : ∀ n, X n ⟶ X (n + 1)
  /-- Each square formed by `step n` and `Spec.map (stepMap n)` is cartesian. -/
  isPullback :
    ∀ n, IsPullback (step n) (hom n) (hom (n + 1)) (Spec.map (ringSystem.stepMap n))
  /-- Each structure morphism is proper. -/
  isProper : ∀ n, IsProper (hom n)
  /-- Each structure morphism is flat. -/
  isFlat : ∀ n, Flat (hom n)
  /-- Each structure morphism is of finite presentation. -/
  finitePresentation : ∀ n, Scheme.Hom.FinitePresentation (hom n)
  /-- Invertible module `L n` on `X n`. -/
  line : ∀ n, (X n).Modules
  /-- Each `L n` is invertible. -/
  invertible : ∀ n, Scheme.Modules.Invertible (line n)
  /-- Comparison isomorphisms `φ_n : (step n)^* L (n + 1) ≅ L n`. -/
  iso : ∀ n, (Scheme.Modules.pullback (step n)).obj (line (n + 1)) ≅ line n
  /-- The invertible module at the initial stage is ample. -/
  isAmpleZero : @Scheme.Modules.IsAmple (X 0) (line 0) (invertible 0)

namespace FormalSystem

/-- Package a sequential ring system, cartesian proper flat finite-presentation
schemes, and compatible invertible modules with ample first stage. -/
def of (ringSystem : SequentialInverseSystem CommRingCat.{u})
    (limitCone : LimitCone ringSystem)
    (ringMapsSurjective : ringSystem.Surjective)
    (kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent)
    (X : ℕ → Scheme.{u}) (hom : ∀ n, X n ⟶ Spec (ringSystem.family n))
    (step : ∀ n, X n ⟶ X (n + 1))
    (isPullback :
      ∀ n, IsPullback (step n) (hom n) (hom (n + 1)) (Spec.map (ringSystem.stepMap n)))
    (isProper : ∀ n, IsProper (hom n)) (isFlat : ∀ n, Flat (hom n))
    (finitePresentation : ∀ n, Scheme.Hom.FinitePresentation (hom n))
    (line : ∀ n, (X n).Modules)
    (invertible : ∀ n, Scheme.Modules.Invertible (line n))
    (iso : ∀ n, (Scheme.Modules.pullback (step n)).obj (line (n + 1)) ≅ line n)
    (isAmpleZero : @Scheme.Modules.IsAmple (X 0) (line 0) (invertible 0)) :
    FormalSystem.{u} where
  ringSystem := ringSystem
  limitCone := limitCone
  ringMapsSurjective := ringMapsSurjective
  kernelsLocallyNilpotent := kernelsLocallyNilpotent
  X := X
  hom := hom
  step := step
  isPullback := isPullback
  isProper := isProper
  isFlat := isFlat
  finitePresentation := finitePresentation
  line := line
  invertible := invertible
  iso := iso
  isAmpleZero := isAmpleZero

/-- `FormalSystem.of` recovers the supplied ring system, limit cone, schemes,
morphisms, line bundles, comparison isomorphisms, and the surjective, locally
nilpotent, cartesian, proper, flat, finite-presentation, invertibility, and
first-stage ampleness conditions. -/
theorem spec (ringSystem : SequentialInverseSystem CommRingCat.{u})
    (limitCone : LimitCone ringSystem)
    (ringMapsSurjective : ringSystem.Surjective)
    (kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent)
    (X : ℕ → Scheme.{u}) (hom : ∀ n, X n ⟶ Spec (ringSystem.family n))
    (step : ∀ n, X n ⟶ X (n + 1))
    (isPullback :
      ∀ n, IsPullback (step n) (hom n) (hom (n + 1)) (Spec.map (ringSystem.stepMap n)))
    (isProper : ∀ n, IsProper (hom n)) (isFlat : ∀ n, Flat (hom n))
    (finitePresentation : ∀ n, Scheme.Hom.FinitePresentation (hom n))
    (line : ∀ n, (X n).Modules)
    (invertible : ∀ n, Scheme.Modules.Invertible (line n))
    (iso : ∀ n, (Scheme.Modules.pullback (step n)).obj (line (n + 1)) ≅ line n)
    (isAmpleZero : @Scheme.Modules.IsAmple (X 0) (line 0) (invertible 0)) :
    let ξ :=
      of ringSystem limitCone ringMapsSurjective kernelsLocallyNilpotent
        X hom step isPullback isProper isFlat finitePresentation
        line invertible iso isAmpleZero
    ξ.ringSystem = ringSystem ∧ ξ.limitCone = limitCone ∧ ξ.X = X ∧
      ξ.hom = hom ∧ ξ.step = step ∧ ξ.line = line ∧ ξ.iso = iso ∧
      ξ.ringMapsSurjective = ringMapsSurjective ∧
      ξ.kernelsLocallyNilpotent = kernelsLocallyNilpotent ∧
      ξ.isPullback = isPullback ∧ ξ.isProper = isProper ∧
      ξ.isFlat = isFlat ∧ ξ.finitePresentation = finitePresentation ∧
      ξ.invertible = invertible ∧ ξ.isAmpleZero = isAmpleZero := sorry

variable (ξ : FormalSystem.{u})

/-- Spectrum of the stage ring `R_n`. -/
def stageSpec (n : ℕ) : Scheme.{u} :=
  Spec (ξ.ringSystem.family n)

/-- `stageSpec n` is `Spec` of the stage ring `R_n`. -/
theorem stageSpec_eq (n : ℕ) :
    ξ.stageSpec n = Spec (ξ.ringSystem.family n) := sorry

/-- Spectrum of the limit ring `R = lim R_n`. -/
def limitSpec : Scheme.{u} :=
  Spec ξ.limitCone.cone.pt

/-- `limitSpec` is `Spec` of the limit ring `R = lim R_n`. -/
theorem limitSpec_eq :
    ξ.limitSpec = Spec ξ.limitCone.cone.pt := sorry

/-- Comparison morphism `S_n ⟶ S` induced by the cone leg `R ⟶ R_n`. -/
def stageToLimit (n : ℕ) : ξ.stageSpec n ⟶ ξ.limitSpec :=
  Spec.map (ξ.limitCone.cone.stageMap n)

/-- `stageToLimit n` is `Spec.map` of the cone leg `R ⟶ R_n`. -/
theorem stageToLimit_eq (n : ℕ) :
    ξ.stageToLimit n = Spec.map (ξ.limitCone.cone.stageMap n) := sorry

/-- Base successor morphism `S_n ⟶ S_{n+1}` induced by `R_{n+1} ⟶ R_n`. -/
def stepBase (n : ℕ) : ξ.stageSpec n ⟶ ξ.stageSpec (n + 1) :=
  Spec.map (ξ.ringSystem.stepMap n)

/-- `stepBase n` is `Spec.map` of the successor transition `R_{n+1} ⟶ R_n`. -/
theorem stepBase_eq (n : ℕ) :
    ξ.stepBase n = Spec.map (ξ.ringSystem.stepMap n) := sorry

/-- The cartesian square identifies `X n` with the fibre product of
`X (n + 1) ⟶ S_{n+1}` along `S_n ⟶ S_{n+1}`. -/
def isoRestrict (n : ℕ) :
    ξ.X n ≅ pullback (ξ.hom (n + 1)) (ξ.stepBase n) :=
  (ξ.isPullback n).isoPullback

/-- The fibre-product comparison commutes with the successor morphism of schemes. -/
theorem isoRestrict_hom_fst (n : ℕ) :
    (ξ.isoRestrict n).hom ≫ pullback.fst (ξ.hom (n + 1)) (ξ.stepBase n) =
      ξ.step n := sorry

/-- The fibre-product comparison commutes with the structure morphism of stage `n`. -/
theorem isoRestrict_hom_snd (n : ℕ) :
    (ξ.isoRestrict n).hom ≫ pullback.snd (ξ.hom (n + 1)) (ξ.stepBase n) =
      ξ.hom n := sorry

end FormalSystem

end AlgebraicGeometry.Polarized
