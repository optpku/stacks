/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local rings along open complements

This leaf provides a local-algebraic condition on the complement of an open
subscheme. It is independent of line bundles and Picard groups.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.OpenComplement

variable {X : Scheme.{u}}

/-- Every local ring at a point of the complement is Noetherian and has Krull
dimension at most one. -/
@[stacks 09NA]
class StalksNoetherianDimLEOne (U : X.Opens) : Prop where
  /-- The pointwise local-algebra condition on the complement. -/
  condition :
    ∀ x : { x : X // x ∉ U },
      IsNoetherianRing (X.presheaf.stalk x.1) ∧
        ringKrullDim (X.presheaf.stalk x.1) ≤ 1

/-- The Noetherian and dimension bound available at one complement stalk. -/
theorem stalk_condition
    (U : X.Opens) [hU : StalksNoetherianDimLEOne U]
    (x : { x : X // x ∉ U }) :
    IsNoetherianRing (X.presheaf.stalk x.1) ∧
      ringKrullDim (X.presheaf.stalk x.1) ≤ 1 := sorry

/-- A bounded-dimensional Noetherian complement has Noetherian local rings. -/
instance instIsNoetherianRing
    (U : X.Opens) [StalksNoetherianDimLEOne U]
    (x : { x : X // x ∉ U }) :
    IsNoetherianRing (X.presheaf.stalk x.1) := sorry

/-- Unfold the local-algebra condition on an open complement. -/
theorem stalksNoetherianDimLEOne_iff (U : X.Opens) :
    StalksNoetherianDimLEOne U ↔
      ∀ x : { x : X // x ∉ U },
        IsNoetherianRing (X.presheaf.stalk x.1) ∧
          ringKrullDim (X.presheaf.stalk x.1) ≤ 1 := sorry

/-- The Krull dimension at a complement stalk is at most one. -/
theorem krullDim_stalk_le_one
    (U : X.Opens) [StalksNoetherianDimLEOne U]
    (x : { x : X // x ∉ U }) :
    ringKrullDim (X.presheaf.stalk x.1) ≤ 1 := sorry

end AlgebraicGeometry.Scheme.OpenComplement
