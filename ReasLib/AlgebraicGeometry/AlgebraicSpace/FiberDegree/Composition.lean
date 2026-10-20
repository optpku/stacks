/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Composition

/-!
# Fibre degrees under composition into algebraic spaces

Fibre-degree bounds multiply when a morphism from a scheme to an algebraic space
is precomposed with a morphism of schemes over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a scheme morphism over `S` has fibre degrees bounded by `n` and a morphism
from a scheme to an algebraic space has fibre degrees bounded by `m`, then their
composite has fibre degrees bounded by `n * m`. -/
theorem degreesOfFibresBoundedBy_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V U : Over S} (φ : V ⟶ U) (f : ofOver U ⟶ X) {n m : ℕ}
    (hφ : Scheme.Hom.degreesOfFibresBoundedBy φ.left n)
    (hf : degreesOfFibresBoundedBy f m) :
    degreesOfFibresBoundedBy (ofOverMap φ ≫ f) (n * m) :=
  sorry

/-- Precomposing a morphism from a scheme to an algebraic space with a scheme
morphism over the base preserves universally bounded fibres when both morphisms
have universally bounded fibres. -/
theorem universallyBoundedFibres_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V U : Over S} (φ : V ⟶ U) (f : ofOver U ⟶ X)
    (hφ : Scheme.Hom.universallyBoundedFibres φ.left) (hf : universallyBoundedFibres f) :
    universallyBoundedFibres (ofOverMap φ ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
