/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Formal smoothness for DVR extensions

The adic formal-smoothness criterion is a reusable extension-level statement.  The source-facing
Chapter 15 file is only a tagged recall of this owner; the ring maps, residue fields, and DVR
extension hypotheses remain explicit here.

@stack 09E7
-/

open IsLocalRing

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

/-- Lemma 15.112.5 (09E7; current Stacks Lemma 15.113.5): an extension of discrete valuation
rings is formally smooth for the `maximalIdeal B`-adic topology exactly when it is weakly
unramified and its residue-field map is separable. -/
@[stacks 09E7 "formal smoothness and weak unramifiedness"]
theorem formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField :
    (algebraMap A B).formally_smooth_for_adic (maximalIdeal B) ↔
      IsExtensionOfDiscreteValuationRings.WeaklyUnramified A B ∧
        Algebra.IsSeparable (ResidueField A) (ResidueField B) := sorry
-- Proof strategy: specialize the adic formal-smoothness/special-fiber criterion to the local map
-- `A → B`; use torsion-freeness of a DVR extension for flatness and identify the closed fiber with
-- `ResidueField B`; translate geometric regularity of this field extension to
-- `Algebra.IsSeparable`; finally rewrite the maximal-ideal condition with
-- `IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal`.
