/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme

/-!
# Length of algebraic-space modules on scheme charts
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The restriction `F|_U` of an `𝒪_X`-module along an étale chart `φ : ofOver U ⟶ X` from a
scheme. -/
abbrev etaleSchemeModule {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules) : U.left.Modules :=
  (restrictToScheme U).obj ((pullback φ).obj F)

/-- `etaleSchemeModule φ F` is the Zariski restriction of the étale pullback of `F`. -/
theorem etaleSchemeModule_eq {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules) :
    etaleSchemeModule φ F = (restrictToScheme U).obj ((pullback φ).obj F) :=
  sorry

/-- The length of `F` at a point of an étale scheme chart, as the length of the Zariski stalk of
`etaleSchemeModule φ F`. -/
def lengthOnEtaleChart {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules) (u : U.left) : ℕ∞ :=
  Module.length (U.left.presheaf.stalk u)
    (RingedSpace.stalkModuleCat (etaleSchemeModule φ F) u)

/-- `lengthOnEtaleChart` is the module length of the Zariski stalk of `etaleSchemeModule φ F`. -/
theorem lengthOnEtaleChart_eq {U : Over S} (φ : ofOver U ⟶ X) (F : X.Modules) (u : U.left) :
    lengthOnEtaleChart φ F u =
      Module.length (U.left.presheaf.stalk u)
        (RingedSpace.stalkModuleCat (etaleSchemeModule φ F) u) :=
  sorry

/-- The length of `F` at `x ∈ |X|` is finite and nonzero: some étale scheme chart over `x` has
strictly positive finite Zariski-stalk length. -/
def hasFiniteNonzeroLengthAt (F : X.Modules) (x : Points X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ ∃ u : U.left,
      Points.mapOfOver φ u = x ∧
        0 < lengthOnEtaleChart φ F u ∧ lengthOnEtaleChart φ F u < ⊤

/-- `hasFiniteNonzeroLengthAt F x` unpacks as existence of an étale scheme chart over `x` with
finite nonzero length. -/
theorem hasFiniteNonzeroLengthAt_iff (F : X.Modules) (x : Points X) :
    hasFiniteNonzeroLengthAt F x ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧
            0 < lengthOnEtaleChart φ F u ∧ lengthOnEtaleChart φ F u < ⊤ :=
  sorry

/-- A given étale scheme chart with finite nonzero length witnesses `hasFiniteNonzeroLengthAt`. -/
theorem hasFiniteNonzeroLengthAt_of_lengthOnEtaleChart {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : X.Modules) {u : U.left} {x : Points X} (hu : Points.mapOfOver φ u = x)
    (hpos : 0 < lengthOnEtaleChart φ F u) (htop : lengthOnEtaleChart φ F u < ⊤) :
    hasFiniteNonzeroLengthAt F x :=
  sorry

/-- An `𝒪_X`-module `F` has length `d` at `x ∈ |X|` if some étale scheme chart over `x`
has Zariski-stalk length `d`. -/
def hasLengthAt (F : X.Modules) (x : Points X) (d : ℕ∞) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ ∃ u : U.left,
      Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d

/-- `hasLengthAt F x d` unpacks as existence of an étale scheme chart over `x` with
Zariski-stalk length `d`. -/
theorem hasLengthAt_iff (F : X.Modules) (x : Points X) (d : ℕ∞) :
    hasLengthAt F x d ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d :=
  sorry

/-- A given étale scheme chart with Zariski-stalk length `d` witnesses `hasLengthAt`. -/
theorem hasLengthAt_of_lengthOnEtaleChart {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : X.Modules) {u : U.left} {x : Points X} {d : ℕ∞}
    (hu : Points.mapOfOver φ u = x) (hd : lengthOnEtaleChart φ F u = d) :
    hasLengthAt F x d :=
  sorry

/-- Finite nonzero length at a point is the existence of a strictly positive finite
length `d` at which `hasLengthAt` holds. -/
theorem hasFiniteNonzeroLengthAt_iff_hasLengthAt (F : X.Modules) (x : Points X) :
    hasFiniteNonzeroLengthAt F x ↔ ∃ d : ℕ∞, 0 < d ∧ d < ⊤ ∧ hasLengthAt F x d :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Modules
