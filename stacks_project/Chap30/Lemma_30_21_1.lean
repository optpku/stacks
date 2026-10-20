/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Criteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.21.1: let `f : X ⟶ S` be a morphism of schemes with `S` locally
Noetherian. Then `f` is finite if and only if `f` is proper and every point-set
fibre is finite. Entries zero and one of the following stronger equivalence for
arbitrary targets imply this locally Noetherian case. -/
@[stacks 02OG] #check
  (AlgebraicGeometry.IsFinite.proper_finiteFibers_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      List.TFAE
        [ AlgebraicGeometry.IsFinite f
        , AlgebraicGeometry.IsProper f ∧
            ∀ s : S, Set.Finite (f ⁻¹' ({s} : Set S))
        , AlgebraicGeometry.IsProper f ∧ AlgebraicGeometry.LocallyQuasiFinite f
        , AlgebraicGeometry.UniversallyClosed f ∧
            AlgebraicGeometry.IsSeparated f ∧
            AlgebraicGeometry.LocallyOfFiniteType f ∧
            ∀ s : S, Set.Finite (f ⁻¹' ({s} : Set S)) ])
