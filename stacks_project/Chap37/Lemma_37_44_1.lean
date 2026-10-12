/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Criteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.44.1: for a morphism of schemes, finiteness is equivalent to properness
with finite point-set fibres, to properness and local quasi-finiteness, and to being
universally closed, separated, locally of finite type, with finite point-set fibres. -/
@[stacks 02LS] #check
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
