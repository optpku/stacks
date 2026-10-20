module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Slicing.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 80.8.1: let `S` be a scheme and let `j : R ⟶ U ⨯ U` be an equivalence
relation on schemes over `S`, encoded as `P : PreRelation U` with
`IsEquivalenceRelation P.t P.s`. If the projections `P.s` and `P.t` are flat and
locally of finite presentation, then there is a morphism `g : U' ⟶ U` over `S`
such that the restricted equivalence relation `R' = (P.pullback g).left` has
projections that are additionally locally quasi-finite, the canonical map
`P.pullbackQuotientMap (StandardTopology.fppf.overTopology S) g` of fppf quotient
sheaves is an isomorphism, and `P.pullbackHom g` maps `R'` into `R`. The object
`U'` may be taken of Stacks size at most `bound (size U)`, hence isomorphic to an
object of `Sch_fppf` whenever `U` is. -/

@[stacks 0489] #check (AlgebraicGeometry.Scheme.PreRelation.existsLocallyQuasiFiniteSlice :
  ∀ {S : Scheme.{u}} {U : Over S} (P : Scheme.PreRelation U)
    [IsEquivalenceRelation P.t P.s]
    [Flat P.s.left] [LocallyOfFinitePresentation P.s.left]
    [Flat P.t.left] [LocallyOfFinitePresentation P.t.left],
    ∃ (U' : Over S) (g : U' ⟶ U),
      Flat (P.pullback g).s.left ∧
        LocallyOfFinitePresentation (P.pullback g).s.left ∧
        LocallyQuasiFinite (P.pullback g).s.left ∧
        Flat (P.pullback g).t.left ∧
        LocallyOfFinitePresentation (P.pullback g).t.left ∧
        LocallyQuasiFinite (P.pullback g).t.left ∧
        IsIso (P.pullbackQuotientMap (StandardTopology.fppf.overTopology S) g) ∧
        U'.left.size ≤ Cardinal.countableSuccBound U.left.size)
