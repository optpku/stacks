module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
import StacksCheckRecall

/-!
# Definition 101.18.2

The finite type point predicate and its set-level API for algebraic stacks are
owned by `ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints`.

@stack 06FY
-/

@[expose] public section

universe u

/- Definition 101.18.2
Let X be an algebraic stack. A point x ∈ Points X is a finite type point when
the equivalent conditions of Lemma 101.18.1 hold (a locally finite type point
would be more accurate). The set of such points is X_ft-pts, recovered as
finiteTypePoints X.
-/
@[stacks 06FY] #check (AlgebraicGeometry.AlgebraicStack.IsFiniteTypePoint :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X],
      AlgebraicGeometry.AlgebraicStack.Points X → Prop)

#check (AlgebraicGeometry.AlgebraicStack.isFiniteTypePoint_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X]
      (x : AlgebraicGeometry.AlgebraicStack.Points X),
        AlgebraicGeometry.AlgebraicStack.IsFiniteTypePoint x ↔
          ∃ p : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X,
            AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType p.hom ∧
              AlgebraicGeometry.AlgebraicStack.Points.mk p = x)

#check (AlgebraicGeometry.AlgebraicStack.finiteTypePoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X],
      Set (AlgebraicGeometry.AlgebraicStack.Points X))

#check (AlgebraicGeometry.AlgebraicStack.mem_finiteTypePoints_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X]
      {x : AlgebraicGeometry.AlgebraicStack.Points X},
        x ∈ AlgebraicGeometry.AlgebraicStack.finiteTypePoints X ↔
          AlgebraicGeometry.AlgebraicStack.IsFiniteTypePoint x)
