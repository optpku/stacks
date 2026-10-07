module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty

/-!
# Locally quasi-finite slices of scheme equivalence relations

An equivalence relation on a scheme over a base, with flat and locally finitely
presented projections, admits a slice whose restricted projections are additionally
locally quasi-finite and whose fppf quotient sheaf is unchanged.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- An equivalence relation on a scheme over `S` whose projections are flat and
locally of finite presentation admits a slice `g : U' ⟶ U` such that the
restricted projections are additionally locally quasi-finite, the canonical map
of fppf quotient sheaves is an isomorphism, and `U'` has Stacks size at most
`bound (size U)`. -/
theorem existsLocallyQuasiFiniteSlice {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [IsEquivalenceRelation P.t P.s]
    [Flat P.s.left] [LocallyOfFinitePresentation P.s.left]
    [Flat P.t.left] [LocallyOfFinitePresentation P.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ U),
      Flat (P.pullback g).s.left ∧
        LocallyOfFinitePresentation (P.pullback g).s.left ∧
        LocallyQuasiFinite (P.pullback g).s.left ∧
        Flat (P.pullback g).t.left ∧
        LocallyOfFinitePresentation (P.pullback g).t.left ∧
        LocallyQuasiFinite (P.pullback g).t.left ∧
        IsIso (P.pullbackQuotientMap (StandardTopology.fppf.overTopology S) g) ∧
        U'.left.size ≤ bound U.left.size :=
  sorry

/-- If `U` lies in a Stacks small bound-closed object property `C`, then a locally
quasi-finite slice may be taken so that `U'` lies in the isomorphism closure of
`C`. -/
theorem existsLocallyQuasiFiniteSlice_isoClosure {S : Scheme.{u}} {U : Over S}
    (P : PreRelation U) [IsEquivalenceRelation P.t P.s]
    [Flat P.s.left] [LocallyOfFinitePresentation P.s.left]
    [Flat P.t.left] [LocallyOfFinitePresentation P.t.left]
    {C : ObjectProperty Scheme.{u}} (hC : IsSmallBoundClosed C) (hU : C U.left) :
    ∃ (U' : Over S) (g : U' ⟶ U),
      Flat (P.pullback g).s.left ∧
        LocallyOfFinitePresentation (P.pullback g).s.left ∧
        LocallyQuasiFinite (P.pullback g).s.left ∧
        Flat (P.pullback g).t.left ∧
        LocallyOfFinitePresentation (P.pullback g).t.left ∧
        LocallyQuasiFinite (P.pullback g).t.left ∧
        IsIso (P.pullbackQuotientMap (StandardTopology.fppf.overTopology S) g) ∧
        U'.left.size ≤ bound U.left.size ∧
        C.isoClosure U'.left :=
  sorry

end AlgebraicGeometry.Scheme.PreRelation
