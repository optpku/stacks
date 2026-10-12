/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_23_3
public import stacks_project.Chap67.Lemma_67_28_2
public import stacks_project.Chap67.Lemma_67_28_3
public import stacks_project.Chap67.Lemma_67_30_3
public import stacks_project.Chap67.Lemma_67_30_4
public import stacks_project.Chap78.Lemma_78_17_1_Restriction

/-!
# Stability of restricted groupoids in algebraic spaces

This module records stability of local finite type, local finite presentation, and
flatness for the source and target maps of a restricted groupoid in algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
  {U' : Over B} (g : U' ⟶ G.U)

/-- Restricting a groupoid along a locally finite-type morphism preserves local finite
type of its source map. -/
instance instPullbackSourceLocallyOfFiniteType
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType g.left] :
    AlgebraicSpace.LocallyOfFiniteType (G.pullback g).s.left := sorry

/-- Restricting a groupoid along a locally finite-type morphism preserves local finite
type of its target map. -/
instance instPullbackTargetLocallyOfFiniteType
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    [AlgebraicSpace.LocallyOfFiniteType g.left] :
    AlgebraicSpace.LocallyOfFiniteType (G.pullback g).t.left := sorry

/-- If the source map, target map, and restriction morphism are locally of finite type,
then both structure maps of the restricted groupoid are locally of finite type. -/
theorem restrictionLocallyOfFiniteType
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    [AlgebraicSpace.LocallyOfFiniteType g.left] :
    AlgebraicSpace.LocallyOfFiniteType (G.pullback g).s.left ∧
      AlgebraicSpace.LocallyOfFiniteType (G.pullback g).t.left := sorry

/-- Restricting a groupoid along a locally finitely presented morphism preserves local
finite presentation of its source map. -/
instance instPullbackSourceLocallyOfFinitePresentation
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation g.left] :
    AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).s.left := sorry

/-- Restricting a groupoid along a locally finitely presented morphism preserves local
finite presentation of its target map. -/
instance instPullbackTargetLocallyOfFinitePresentation
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation g.left] :
    AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).t.left := sorry

/-- If the source map, target map, and restriction morphism are locally of finite
presentation, then both structure maps of the restricted groupoid are locally of
finite presentation. -/
theorem restrictionLocallyOfFinitePresentation
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation g.left] :
    AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).s.left ∧
      AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).t.left := sorry

/-- Restricting a groupoid along a flat morphism preserves flatness of its source map. -/
instance instPullbackSourceFlat [AlgebraicSpace.Flat G.s.left]
    [AlgebraicSpace.Flat g.left] : AlgebraicSpace.Flat (G.pullback g).s.left := sorry

/-- Restricting a groupoid along a flat morphism preserves flatness of its target map. -/
instance instPullbackTargetFlat [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.Flat g.left] : AlgebraicSpace.Flat (G.pullback g).t.left := sorry

/-- If the source map, target map, and restriction morphism are flat, then both
structure maps of the restricted groupoid are flat. -/
theorem restrictionFlat [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.Flat g.left] :
    AlgebraicSpace.Flat (G.pullback g).s.left ∧
      AlgebraicSpace.Flat (G.pullback g).t.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
