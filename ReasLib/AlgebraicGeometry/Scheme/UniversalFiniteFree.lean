/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.RingTheory.Algebra.UniversalFiniteFree

@[expose] public section

open CategoryTheory

noncomputable section

namespace UniversalFiniteFreeAlgebra

/-- The affine base scheme `X_d = Spec(A_d)` of the universal finite free algebra. -/
abbrev baseScheme (d : ℕ+) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (CoefficientRing d))

/-- The affine family scheme `Y_d = Spec(B_d)` of the universal finite free algebra. -/
abbrev familyScheme (d : ℕ+) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (UniversalAlgebra d))

/-- The universal finite free projection, obtained by applying `Spec.map` to the algebra map. -/
def projection (d : ℕ+) : familyScheme d ⟶ baseScheme d :=
  AlgebraicGeometry.Spec.map (structureMap d)

/-- The universal projection is finite locally free of rank `d`. -/
instance projectionIsFiniteLocallyFreeOfRank (d : ℕ+) :
    AlgebraicGeometry.IsFiniteLocallyFreeOfRank (projection d) d := sorry

end UniversalFiniteFreeAlgebra
