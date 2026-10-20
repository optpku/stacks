module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_3_3
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_7_4_Points

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Canonical topology on the points of an algebraic stack

Open subsets are detected by flat locally-of-finite-presentation morphisms
from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Points.isOpen_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (s : Set (Points X)),
    IsOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : U.toGroupoids ⟶ X)
        [Groupoids.Hom.Flat p] [Groupoids.Hom.LocallyOfFinitePresentation p],
        IsOpen (Points.mapSpace p ⁻¹' s))

end AlgebraicGeometry.AlgebraicStack
