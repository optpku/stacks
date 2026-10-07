module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Stability

@[expose] public section

open CategoryTheory

universe u

/- Lemma 40.9.1 (1): restriction preserves local finite type of both structure maps when
the original source and target maps and the restriction morphism are locally of finite type. -/
@[stacks 04MP] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionLocallyOfFiniteType :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {U' : Over S} (g : U' ⟶ G.U) [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.LocallyOfFiniteType G.t.left]
      [AlgebraicGeometry.LocallyOfFiniteType g.left],
      AlgebraicGeometry.LocallyOfFiniteType (G.pullback g).s.left ∧
        AlgebraicGeometry.LocallyOfFiniteType (G.pullback g).t.left)

/- Lemma 40.9.1 (2): restriction preserves local finite presentation of both structure maps
when the original source and target maps and the restriction morphism are locally of finite
presentation. -/
@[stacks 04MP] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionLocallyOfFinitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {U' : Over S} (g : U' ⟶ G.U)
      [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
      [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
      [AlgebraicGeometry.LocallyOfFinitePresentation g.left],
      AlgebraicGeometry.LocallyOfFinitePresentation (G.pullback g).s.left ∧
        AlgebraicGeometry.LocallyOfFinitePresentation (G.pullback g).t.left)

/- Lemma 40.9.1 (3): restriction preserves flatness of both structure maps when the
original source and target maps and the restriction morphism are flat. -/
@[stacks 04MP] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionFlat :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {U' : Over S} (g : U' ⟶ G.U) [AlgebraicGeometry.Flat G.s.left]
      [AlgebraicGeometry.Flat G.t.left] [AlgebraicGeometry.Flat g.left],
      AlgebraicGeometry.Flat (G.pullback g).s.left ∧
        AlgebraicGeometry.Flat (G.pullback g).t.left)
