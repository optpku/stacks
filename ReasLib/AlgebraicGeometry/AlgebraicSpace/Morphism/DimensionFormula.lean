/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Dimension formulas for morphisms of algebraic spaces

A flat, locally finite-type morphism of locally Noetherian algebraic spaces
of relative dimension `d` adds `d` to local dimension at every source point.
For a locally finite-type morphism with locally Noetherian target, local-ring
dimension plus residue-field transcendence degree is bounded by the dimension
at the image plus the greatest degree at dimension-zero points specializing to
the source point. This greatest degree exists.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat, locally finite-type morphism of locally Noetherian algebraic spaces
of relative dimension `d` has source dimension at each point equal to the
dimension at its image plus `d`. -/
@[stacks 0AFH]
theorem dimensionAt_eq_image_add_relativeDimension_of_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {d : ℕ} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    [LocallyOfFiniteType f] [RelativeDimension f d] (x : Points X) :
    dimensionAt x = dimensionAt (Points.map f x) + (d : WithBot ℕ∞) :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, the residue-field transcendence degrees at dimension-zero points
specializing to a given point have a greatest natural-number value. -/
theorem exists_isGreatest_residueFieldTrdegAt_specializing
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : Points X) :
    ∃ E : ℕ, IsGreatest {n | ∃ ξ : Points X,
      ξ ⤳ x ∧ localRingDimAt ξ = 0 ∧ n = residueFieldTrdegAt f ξ} E :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, the local-ring dimension at a source point plus its residue-field
transcendence degree is at most the local-ring dimension at its image plus the
greatest transcendence degree at dimension-zero points specializing to it. -/
@[stacks 0BAX]
theorem localRingDimAt_add_trdeg_le_genericMax
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (x : Points X) (E : ℕ)
    (hE : IsGreatest {n | ∃ ξ : Points X,
      ξ ⤳ x ∧ localRingDimAt ξ = 0 ∧ n = residueFieldTrdegAt f ξ} E) :
    localRingDimAt x + (residueFieldTrdegAt f x : WithBot ℕ∞) ≤
      localRingDimAt (Points.map f x) + (E : WithBot ℕ∞) :=
  sorry

/-- The supremum of residue-field transcendence degrees of `f` at points of `|X|`
where the local ring of `X` has dimension `0`. -/
noncomputable def localRingDimZeroTrdeg {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : ℕ∞ :=
  ⨆ ξ : Points X, ⨆ _ : localRingDimAt ξ = 0, residueFieldTranscendenceDegreeAt f ξ

/-- The residue-field transcendence degree of `f` at a point of local-ring
dimension `0` is at most `localRingDimZeroTrdeg f`. -/
theorem le_localRingDimZeroTrdeg {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {ξ : Points X} (hξ : localRingDimAt ξ = 0) :
    residueFieldTranscendenceDegreeAt f ξ ≤ localRingDimZeroTrdeg f :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces with locally Noetherian
target, the dimension of the source is at most the dimension of the target plus
the supremum of residue-field transcendence degrees at source points whose local
rings have dimension zero. -/
@[stacks 0BAY]
theorem dimension_le_add_localRingDimZeroTrdeg
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    dimension X ≤ dimension Y + (localRingDimZeroTrdeg f : WithBot ℕ∞) :=
  sorry

/-- A dominant locally finite-type morphism of integral algebraic spaces with
locally Noetherian target has source dimension bounded by target dimension plus
the residue-field transcendence degree at a generic source point. -/
@[stacks 0EDC]
theorem dimension_le_add_residueFieldTrdegAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Dominant f] [LocallyOfFiniteType f] {x : Points X}
    (hx : x ∈ genericPoints X) :
    dimension X ≤ dimension Y + (residueFieldTrdegAt f x : WithBot ℕ∞) :=
  sorry

/-- A proper dominant morphism of integral algebraic spaces with locally
Noetherian target has source dimension equal to target dimension plus the
residue-field transcendence degree at a generic source point. -/
@[stacks 0EDC]
theorem dimension_eq_add_residueFieldTrdegAt_of_proper {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Dominant f] [Proper f] {x : Points X}
    (hx : x ∈ genericPoints X) :
    dimension X = dimension Y + (residueFieldTrdegAt f x : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
