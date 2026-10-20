/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.InseparableAffineLine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.InseparableAffineLine
open AlgebraicGeometry.RationalFunctionRegularityCounterexample

/- Exercise 111.33.17 (1): the affine line over the purely inseparable extension
of `BaseField p` is an integral scheme. -/
@[stacks 0292] #check (AlgebraicGeometry.InseparableAffineLine.instIsIntegralScheme :
  ∀ (p : ℕ) [Fact p.Prime], IsIntegral (scheme p))

/- Exercise 111.33.17 (2): this scheme is 1-dimensional. -/
@[stacks 0292] #check (AlgebraicGeometry.InseparableAffineLine.topologicalKrullDim_eq_one :
  ∀ (p : ℕ) [Fact p.Prime], topologicalKrullDim (scheme p) = 1)

/- Exercise 111.33.17 (3): the structure morphism to `Spec (BaseField p)` is of
finite type. -/
@[stacks 0292] #check (AlgebraicGeometry.InseparableAffineLine.instFiniteTypeToBase :
  ∀ (p : ℕ) [Fact p.Prime], Scheme.Hom.FiniteType (toBase p))

/- Exercise 111.33.17 (4): after the finite field extension
`ExtensionField p / BaseField p`, the fiber product is not reduced. -/
@[stacks 0292] #check (AlgebraicGeometry.InseparableAffineLine.finiteFieldExtension_pullback_not_isReduced :
  ∀ (p : ℕ) [Fact p.Prime],
    FiniteDimensional (BaseField p) (ExtensionField p) ∧
      ¬ IsReduced (baseChange p))
