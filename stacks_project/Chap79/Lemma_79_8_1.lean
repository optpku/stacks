module

import StacksCheckRecall
public import stacks_project.Chap79.Lemma_79_8_1_Stability

@[expose] public section

open CategoryTheory

universe u

/- Lemma 79.8.1 (1): restriction preserves local finite type of both structure maps when
the original source and target maps and the restriction morphism are locally of finite type. -/
@[stacks 04RP] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionLocallyOfFiniteType :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B)
      {U' : Over B} (g : U' ⟶ G.U)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType G.t.left]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType g.left],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType (G.pullback g).s.left ∧
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType (G.pullback g).t.left)

/- Lemma 79.8.1 (2): restriction preserves local finite presentation of both structure maps
when the original source and target maps and the restriction morphism are locally of finite
presentation. -/
@[stacks 04RP] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionLocallyOfFinitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B)
      {U' : Over B} (g : U' ⟶ G.U)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation g.left],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).s.left ∧
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).t.left)

/- Lemma 79.8.1 (3): restriction preserves flatness of both structure maps when the
original source and target maps and the restriction morphism are flat. -/
@[stacks 04RP] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionFlat :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B)
      {U' : Over B} (g : U' ⟶ G.U) [AlgebraicGeometry.AlgebraicSpace.Flat G.s.left]
      [AlgebraicGeometry.AlgebraicSpace.Flat G.t.left]
      [AlgebraicGeometry.AlgebraicSpace.Flat g.left],
      AlgebraicGeometry.AlgebraicSpace.Flat (G.pullback g).s.left ∧
        AlgebraicGeometry.AlgebraicSpace.Flat (G.pullback g).t.left)
