/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Dimension

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 33.5.2 (1): the closed-fibre dimension and residue-field transcendence-degree
formula after extending the base field. -/
@[stacks 0C4Z] #check
  (AlgebraicGeometry.FieldExtension.Stalk.ClosedFiber.ringKrullDim_add_trdeg_eq :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (y : FieldExtension.baseChange k K f),
      ringKrullDim (FieldExtension.Stalk.ClosedFiber.quotient k K f y) +
          Cardinal.toNat (Algebra.trdeg K ((FieldExtension.baseChange k K f).residueField y)) =
        Cardinal.toNat
          (Algebra.trdeg k
            (X.residueField (FieldExtension.toSource k K f y))))

/- Lemma 33.5.2 (2): the closed-fibre, source-stalk, and base-change-stalk dimension
formula after extending the base field. -/
@[stacks 0C4Z] #check
  (AlgebraicGeometry.FieldExtension.Stalk.ClosedFiber.ringKrullDim_add_sourceStalk_eq_baseChangeStalk :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      (y : FieldExtension.baseChange k K f),
      ringKrullDim (FieldExtension.Stalk.ClosedFiber.quotient k K f y) +
          ringKrullDim (X.presheaf.stalk (FieldExtension.toSource k K f y)) =
        ringKrullDim ((FieldExtension.baseChange k K f).presheaf.stalk y))

end AlgebraicGeometry
