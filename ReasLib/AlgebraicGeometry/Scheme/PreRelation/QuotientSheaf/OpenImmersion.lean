/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Pullback

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Restricting an equivalence relation with surjective, flat, locally finitely presented
projections along a flat, locally finitely presented morphism induces a representable open
immersion of fppf quotient sheaves. -/
theorem pullbackQuotientMap_isOpenImmersion {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s]
    [Surjective P.t.left] [Surjective P.s.left] [Flat P.t.left] [Flat P.s.left]
    [LocallyOfFinitePresentation P.t.left] [LocallyOfFinitePresentation P.s.left]
    [Flat g.left] [LocallyOfFinitePresentation g.left] :
    (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{u + 1}
      (P.pullbackQuotientMap (Scheme.fppfTopology.over S) g).hom := sorry

/-- Restricting an equivalence relation with surjective, flat, locally finitely presented
projections along a flat, locally finitely presented morphism induces a relatively
representable map of fppf quotient sheaves with respect to `uliftYoneda`. -/
theorem pullbackQuotientMap_relativelyRepresentable {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s]
    [Surjective P.t.left] [Surjective P.s.left] [Flat P.t.left] [Flat P.s.left]
    [LocallyOfFinitePresentation P.t.left] [LocallyOfFinitePresentation P.s.left]
    [Flat g.left] [LocallyOfFinitePresentation g.left] :
    uliftYoneda.{u + 1}.relativelyRepresentable
      (P.pullbackQuotientMap (Scheme.fppfTopology.over S) g).hom := sorry

/-- A represented pullback of the map of fppf quotient sheaves induced by restriction
along a flat, locally finitely presented morphism is an open immersion when the relation
is an equivalence relation with surjective, flat, locally finitely presented projections. -/
theorem isOpenImmersion_of_isPullback_pullbackQuotientMap {S : Scheme.{u}} {U U' : Over S}
    (P : PreRelation U) (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s]
    [Surjective P.t.left] [Surjective P.s.left] [Flat P.t.left] [Flat P.s.left]
    [LocallyOfFinitePresentation P.t.left] [LocallyOfFinitePresentation P.s.left]
    [Flat g.left] [LocallyOfFinitePresentation g.left] {T W : Over S}
    {ξ : uliftYoneda.{u + 1}.obj T ⟶
      (P.quotientSheaf (Scheme.fppfTopology.over S)).obj}
    {fst : uliftYoneda.{u + 1}.obj W ⟶
      ((P.pullback g).quotientSheaf (Scheme.fppfTopology.over S)).obj}
    {snd : W ⟶ T}
    (h_pullback : IsPullback fst (uliftYoneda.{u + 1}.map snd)
      (P.pullbackQuotientMap (Scheme.fppfTopology.over S) g).hom ξ) :
    IsOpenImmersion snd.left := sorry

end AlgebraicGeometry.Scheme.PreRelation
