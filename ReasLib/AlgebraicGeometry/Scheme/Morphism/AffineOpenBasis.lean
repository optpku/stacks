/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- For a morphism of schemes, the affine opens of the source that map into an affine open of
the target form a basis for the topology of the source. -/
theorem isBasis_affineOpens_mappingIntoAffineOpen (f : X ⟶ S) :
    TopologicalSpace.Opens.IsBasis
      {U : X.Opens | IsAffineOpen U ∧ ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V} := sorry

end AlgebraicGeometry.Scheme.Hom
