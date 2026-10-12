/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 65.10.2: let `S` be a scheme, let `U` be a scheme over `S`, and let `P` be a
pre-relation on `U` whose projections `P.t` and `P.s` form an equivalence relation and
are surjective, flat, and locally of finite presentation. Let `g : U' ⟶ U` be flat and
locally of finite presentation, and write `R'` for the restriction `P.pullback g`. Then
the induced map of fppf quotient sheaves `U'/R' ⟶ U/R`, namely
`P.pullbackQuotientMap (Scheme.fppfTopology.over S) g`, is representable and an open
immersion. -/
@[stacks 02WU] #check
  (AlgebraicGeometry.Scheme.PreRelation.pullbackQuotientMap_isOpenImmersion :
    ∀ {S : Scheme.{u}} {U U' : Over S}
    (P : Scheme.PreRelation U) (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s]
    [Surjective P.t.left] [Surjective P.s.left] [Flat P.t.left] [Flat P.s.left]
    [LocallyOfFinitePresentation P.t.left] [LocallyOfFinitePresentation P.s.left]
    [Flat g.left] [LocallyOfFinitePresentation g.left],
    (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{u + 1}
      (P.pullbackQuotientMap (Scheme.fppfTopology.over S) g).hom)
