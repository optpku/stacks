/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Instances.ZMod
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open scoped PowerSeries.WithPiTopology

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Continuous rank-`n` power-series representations of the arithmetic étale fundamental group. -/
abbrev GLPowerSeriesRep {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    (n ℓ : ℕ) (xbar : GeometricPoint (geometricBaseChange X)) :=
  ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
    (GL (Fin n) (PowerSeries (ZMod ℓ)))

/-- A representation has finite geometric monodromy when its restriction to the geometric
étale fundamental group has finite image. -/
def HasFiniteGeometricMonodromy {k : Type u} [Field k] {X : SchemeOverField k}
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)] {n ℓ : ℕ}
    {xbar : GeometricPoint (geometricBaseChange X)}
    (ρ : GLPowerSeriesRep X n ℓ xbar) : Prop :=
  Set.Finite (Set.range (ρ.comp (geometricToArithmetic X xbar).hom))

/-- Finite geometric monodromy is equivalent to finiteness of the subgroup image of the
geometric restriction of the representation. -/
theorem hasFiniteGeometricMonodromy_iff {k : Type u} [Field k] {X : SchemeOverField k}
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)] {n ℓ : ℕ}
    {xbar : GeometricPoint (geometricBaseChange X)} (ρ : GLPowerSeriesRep X n ℓ xbar) :
    HasFiniteGeometricMonodromy ρ ↔
      Finite (MonoidHom.range (ρ.comp (geometricToArithmetic X xbar).hom).toMonoidHom) :=
  Iff.rfl

/-- De Jong's conjecture for rank `n` on a geometrically irreducible smooth projective curve
over a finite field: all continuous power-series representations have finite geometric monodromy. -/
def deJongConjecture {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)] (n : ℕ) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (xbar : GeometricPoint (geometricBaseChange X))
    (ρ : GLPowerSeriesRep X n ℓ xbar), HasFiniteGeometricMonodromy ρ

/-- De Jong's conjecture is the finite-geometric-monodromy assertion for every prime,
geometric base point, and continuous rank-`n` power-series representation. -/
theorem deJongConjecture_iff {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)] (n : ℕ) :
    deJongConjecture X n ↔
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (xbar : GeometricPoint (geometricBaseChange X))
        (ρ : GLPowerSeriesRep X n ℓ xbar), HasFiniteGeometricMonodromy ρ :=
  Iff.rfl

/-- De Jong's conjecture holds in ranks at most two for a geometrically irreducible smooth
projective curve over a finite field. -/
theorem deJongConjecture_of_le_two {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)] {n : ℕ} (hn : n ≤ 2) :
    deJongConjecture X n := sorry

/-- A continuous power-series representation of rank at most two on a geometrically
irreducible smooth projective curve over a finite field has finite geometric monodromy. -/
theorem hasFiniteGeometricMonodromy_of_nat_le_two
    {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)] {n : ℕ} (hn : n ≤ 2) {ℓ : ℕ} [Fact ℓ.Prime]
    (xbar : GeometricPoint (geometricBaseChange X)) (ρ : GLPowerSeriesRep X n ℓ xbar) :
    HasFiniteGeometricMonodromy ρ :=
  deJongConjecture_of_le_two X hn ℓ xbar ρ

/-- de Jong's conjecture at a fixed prime `ℓ`, geometric base point `xbar`, and rank `n`
asserts finite geometric monodromy for every continuous rank-`n` power-series representation. -/
def deJongConjectureAt {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) (ℓ n : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ ρ : GLPowerSeriesRep X n ℓ xbar, HasFiniteGeometricMonodromy ρ

/-- The fixed-prime de Jong conjecture is finite geometric monodromy for every continuous power-series representation. -/
theorem deJongConjectureAt_iff {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) (ℓ n : ℕ) [Fact ℓ.Prime] :
    deJongConjectureAt X xbar ℓ n ↔
      ∀ ρ : etaleFundamentalGroup X.left (arithmeticPoint X xbar) →ₜ*
          GL (Fin n) (PowerSeries (ZMod ℓ)),
        HasFiniteGeometricMonodromy ρ :=
  Iff.rfl

/-- De Jong's conjecture holds in rank `n` for a geometrically irreducible smooth
projective curve over a finite field when the coefficient prime `ℓ` differs from the
field characteristic and `2 * n < ℓ`. -/
theorem deJongConjectureAt_of_prime_gt_two_mul
    {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hℓk : (ℓ : k) ≠ 0) (hℓ : 2 * n < ℓ) :
    deJongConjectureAt X xbar ℓ n := sorry

/-- A continuous rank-`n` power-series representation on a geometrically irreducible
smooth projective curve over a finite field has finite geometric monodromy when the
coefficient prime `ℓ` differs from the field characteristic and `2 * n < ℓ`. -/
theorem hasFiniteGeometricMonodromy_of_prime_gt_two_mul
    {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hℓk : (ℓ : k) ≠ 0) (hℓ : 2 * n < ℓ) (ρ : GLPowerSeriesRep X n ℓ xbar) :
    HasFiniteGeometricMonodromy ρ :=
  deJongConjectureAt_of_prime_gt_two_mul X xbar hℓk hℓ ρ

end AlgebraicGeometry.SchemeOverField
