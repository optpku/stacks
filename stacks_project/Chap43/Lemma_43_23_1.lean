/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection.Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/- Lemma 43.23.1: a proper closed subscheme of `ℙ(V)` admits a nonempty open locus
of closed projection centers such that every restricted linear projection is finite. -/
@[stacks 0B1P] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection.exists_open_isFinite_restrict :
    ∀ (n : ℕ), Module.finrank k V = n + 1 →
      ∀ {X : Scheme.{u}}
        (i : X ⟶ ProjectiveSpace.VectorSpace.scheme k V) [IsClosedImmersion i],
        Set.range i.base ≠ Set.univ →
          ∀ (projection : ∀ (p : ProjectiveSpace.VectorSpace.scheme k V),
            IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V)) →
              ProjectiveSpace.VectorSpace.LinearProjection k V p),
            ∃ U : (ProjectiveSpace.VectorSpace.scheme k V).Opens, Nonempty U ∧
              ∀ (p : ProjectiveSpace.VectorSpace.scheme k V), p ∈ U →
                (hp : IsClosed ({p} : Set (ProjectiveSpace.VectorSpace.scheme k V))) →
                  p ∉ Set.range i.base ∧
                    ∀ hpi : p ∉ Set.range i.base,
                      IsFinite ((projection p hp).restrict i
                        ((projection p hp).range_subset_domain i hpi)))
