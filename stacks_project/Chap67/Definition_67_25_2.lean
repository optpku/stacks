/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint
import StacksCheckRecall

/-!
# Definition 67.25.2

The finite type point predicate and its set-level API for algebraic spaces are
owned by `stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint`.

@stack 06EG
-/

@[expose] public section

universe u

/- Definition 67.25.2
Let S be a scheme and let X be an algebraic space over S. A point x ∈ Points X
is a finite type point when the equivalent conditions of Lemma 67.25.1 hold.
The set of such points is X_ft-pts, recovered as finiteTypePoints X.
-/
@[stacks 06EG] #check (@AlgebraicGeometry.AlgebraicSpace.IsFiniteTypePoint :
  {S : AlgebraicGeometry.Scheme.{u}} → {X : AlgebraicGeometry.AlgebraicSpace S} →
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)

#check (@AlgebraicGeometry.AlgebraicSpace.isFiniteTypePoint_iff :
  {S : AlgebraicGeometry.Scheme.{u}} → {X : AlgebraicGeometry.AlgebraicSpace S} →
    (x : AlgebraicGeometry.AlgebraicSpace.Points X) →
      AlgebraicGeometry.AlgebraicSpace.IsFiniteTypePoint x ↔
        ∃ p : AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint X,
          AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType p.hom ∧
            AlgebraicGeometry.AlgebraicSpace.Points.mk p = x)

#check (@AlgebraicGeometry.AlgebraicSpace.finiteTypePoints :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.AlgebraicSpace S) →
    Set (AlgebraicGeometry.AlgebraicSpace.Points X))

#check (@AlgebraicGeometry.AlgebraicSpace.mem_finiteTypePoints_iff :
  {S : AlgebraicGeometry.Scheme.{u}} → {X : AlgebraicGeometry.AlgebraicSpace S} →
    {x : AlgebraicGeometry.AlgebraicSpace.Points X} →
      x ∈ AlgebraicGeometry.AlgebraicSpace.finiteTypePoints X ↔
        AlgebraicGeometry.AlgebraicSpace.IsFiniteTypePoint x)
