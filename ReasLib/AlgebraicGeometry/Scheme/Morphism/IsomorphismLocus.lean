/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Isomorphism loci of scheme morphisms

This file defines the largest open subset of the target over which a scheme morphism is an
isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The maximal open subset of the target over which a scheme morphism restricts to an
isomorphism. -/
def isomorphismLocus (f : X ⟶ Y) : Y.Opens :=
  sSup {U : Y.Opens | IsIso (f ∣_ U)}

/-- A point lies in the isomorphism locus exactly when it has an open neighborhood over which
the morphism restricts to an isomorphism. -/
theorem mem_isomorphismLocus (f : X ⟶ Y) (y : Y) :
    y ∈ f.isomorphismLocus ↔ ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := sorry

/-- Every target open over which the morphism restricts to an isomorphism is contained in its
isomorphism locus. -/
theorem isomorphismLocus_maximal (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] :
    U ≤ f.isomorphismLocus := sorry

/-- Restriction to the isomorphism locus is an isomorphism. -/
instance instIsIsoRestrictIsomorphismLocus (f : X ⟶ Y) :
    IsIso (f ∣_ f.isomorphismLocus) := sorry

end Scheme.Hom
end AlgebraicGeometry
