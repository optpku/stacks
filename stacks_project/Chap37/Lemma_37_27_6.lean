module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.IrreducibleComponents

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.27.6: for a finite-type morphism, the geometric irreducible-fibre
component count is constant on a nonempty open of the reduced closure of any point. -/
@[stacks 055A] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_geometricIrreducibleFiberComponentCount_eq :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] (y : Y),
      ∃ V : (AlgebraicGeometry.Scheme.PointClosure.scheme y).Opens, Nonempty V ∧
        ∃ c : ℕ∞, ∀ z : AlgebraicGeometry.Scheme.PointClosure.scheme y, z ∈ V →
          f.geometricIrreducibleFiberComponentCount
            (AlgebraicGeometry.Scheme.PointClosure.ι y z) = c)
