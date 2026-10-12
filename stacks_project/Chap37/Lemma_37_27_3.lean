/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.IrreducibleComponents

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.27.3 (1): the geometric irreducible-fibre component count can be
computed over any separably closed extension of the residue field. -/
@[stacks 0556] #check
  (AlgebraicGeometry.Scheme.Hom.geometricIrreducibleFiberComponentCount_eq_enatCard :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
      [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K],
      f.geometricIrreducibleFiberComponentCount y =
        ENat.card
          (irreducibleComponents
            (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y) K
              (f.fiberToSpecResidueField y))))

/- Lemma 37.27.3 (2): the number of geometric irreducible components of the
fibres of a scheme morphism is invariant under arbitrary base change. -/
@[stacks 0556] #check
  (AlgebraicGeometry.Scheme.Hom.geometricIrreducibleFiberComponentCount_baseChange :
    ∀ {Y X Y' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g),
      f'.geometricIrreducibleFiberComponentCount =
        fun y' ↦ f.geometricIrreducibleFiberComponentCount (g y'))
