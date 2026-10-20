/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection

/-!
# Finite restrictions of linear projections

This file records a generic finiteness result for the restriction of a linear projection to a
proper closed subscheme of projective space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A proper closed subscheme of `ℙ(V)` admits a nonempty open locus of closed projection
centers such that every associated restricted linear projection is finite. -/
theorem exists_open_isFinite_restrict
    (n : ℕ) (hV : Module.finrank k V = n + 1)
    {X : Scheme.{u}}
    (i : X ⟶ scheme k V) [IsClosedImmersion i]
    (hX : Set.range i.base ≠ Set.univ)
    (projection : ∀ (p : scheme k V),
      IsClosed ({p} : Set (scheme k V)) → LinearProjection k V p) :
    ∃ U : (scheme k V).Opens, Nonempty U ∧
      ∀ (p : scheme k V), p ∈ U →
        (hp : IsClosed ({p} : Set (scheme k V))) →
          p ∉ Set.range i.base ∧
            ∀ hpi : p ∉ Set.range i.base,
              IsFinite ((projection p hp).restrict i
                ((projection p hp).range_subset_domain i hpi)) := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection
