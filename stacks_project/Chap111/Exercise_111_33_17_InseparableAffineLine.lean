/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.RationalFunctionCounterexample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# The inseparable affine line over `𝔽_p(t)`

This file constructs the affine line over the purely inseparable extension
`AdjoinRoot (InseparablePoint.polynomial p)` of `BaseField p` and records that
it is an integral 1-dimensional finite-type scheme whose base change along that
finite extension is not reduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry.RationalFunctionRegularityCounterexample

namespace AlgebraicGeometry.InseparableAffineLine

/-- The purely inseparable extension of `BaseField p` obtained by adjoining a
root of `InseparablePoint.polynomial p`. -/
abbrev ExtensionField (p : ℕ) [Fact p.Prime] : Type :=
  AdjoinRoot (InseparablePoint.polynomial p)

/-- `InseparablePoint.polynomial p` is irreducible over `BaseField p`. -/
instance instIrreduciblePolynomial (p : ℕ) [Fact p.Prime] :
    Fact (Irreducible (InseparablePoint.polynomial p)) := sorry

/-- The coordinate ring of the affine line over `ExtensionField p`. -/
abbrev CoordinateRing (p : ℕ) [Fact p.Prime] : Type :=
  Polynomial (ExtensionField p)

/-- The affine line over `ExtensionField p`. -/
def scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (CoordinateRing p))

/-- The structure morphism from the affine line over `ExtensionField p` to
`Spec (BaseField p)`. -/
def toBase (p : ℕ) [Fact p.Prime] :
    scheme p ⟶ Spec (CommRingCat.of (BaseField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) (CoordinateRing p)))

/-- The affine line over `ExtensionField p`, viewed as a scheme over
`Spec (BaseField p)`. -/
def overBase (p : ℕ) [Fact p.Prime] :
    Over (Spec (CommRingCat.of (BaseField p))) :=
  Over.mk (toBase p)

/-- The fiber product of `scheme p` with `Spec (ExtensionField p)` over
`Spec (BaseField p)`. -/
def baseChange (p : ℕ) [Fact p.Prime] : Scheme :=
  FieldExtension.baseChange (BaseField p) (ExtensionField p) (toBase p)

/-- The affine line over `ExtensionField p` is an integral scheme. -/
instance instIsIntegralScheme (p : ℕ) [Fact p.Prime] :
    IsIntegral (scheme p) := sorry

/-- The affine line over `ExtensionField p` is 1-dimensional. -/
theorem topologicalKrullDim_eq_one (p : ℕ) [Fact p.Prime] :
    topologicalKrullDim (scheme p) = 1 := sorry

/-- The structure morphism `toBase p` is of finite type. -/
instance instFiniteTypeToBase (p : ℕ) [Fact p.Prime] :
    Scheme.Hom.FiniteType (toBase p) := sorry

/-- `ExtensionField p` is a finite extension of `BaseField p`. -/
instance instFiniteDimensionalExtension (p : ℕ) [Fact p.Prime] :
    FiniteDimensional (BaseField p) (ExtensionField p) := sorry

/-- The fiber product along `ExtensionField p / BaseField p` is not reduced. -/
theorem not_isReduced_baseChange (p : ℕ) [Fact p.Prime] :
    ¬ IsReduced (baseChange p) := sorry

/-- `ExtensionField p / BaseField p` is a finite field extension along which the
fiber product of `scheme p` is not reduced. -/
theorem finiteFieldExtension_pullback_not_isReduced (p : ℕ) [Fact p.Prime] :
    FiniteDimensional (BaseField p) (ExtensionField p) ∧
      ¬ IsReduced (baseChange p) := sorry

end AlgebraicGeometry.InseparableAffineLine
