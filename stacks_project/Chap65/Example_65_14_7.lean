/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

/- Example 65.14.7 (1): the canonical Galois action on the spectrum of the complex
algebraic numbers over the rational spectrum is residue-field free and defines an
étale equivalence relation. -/
@[stacks 02Z6] #check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.instIsResidueFieldFree_action :
  AlgebraicGeometry.Scheme.PreRelation.IsResidueFieldFree
    AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action)

#check (AlgebraicGeometry.Scheme.PreRelation.instIsEtaleEquivalenceRelation_ofAut
    AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action :
  (AlgebraicGeometry.Scheme.PreRelation.ofAut
    AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action).IsEtaleEquivalenceRelation)

/- Example 65.14.7 (2): the fppf quotient is an algebraic space over the rational
spectrum, with its canonical representable étale locally-surjective atlas. -/
@[stacks 02Z6] #check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints :
  Sheaf
    (Scheme.fppfTopology.over AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.base)
    (Type 1))

#check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints_spec :
  uliftYoneda.{1}.relativelyRepresentable
      (diag AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.sheafOfPoints.obj) ∧
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{1}
      AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.atlas.hom ∧
    Presheaf.IsLocallySurjective
      (Scheme.etaleTopology.over AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.base)
      AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.atlas.hom)

/- Example 65.14.7 (3): the finite Galois subgroups are trivial or conjugate to the
order-two conjugation subgroup, which fixes the real algebraic numbers. -/
@[stacks 02Z6] #check (AlgebraicNumbers.finite_subgroup_eq_bot_or_isConj :
  ∀ (H : Subgroup AlgebraicNumbers.gal) [Finite H],
    H = ⊥ ∨ ∃ g : AlgebraicNumbers.gal,
      H = AlgebraicNumbers.complexConjSubgroup.map (MulAut.conj g).toMonoidHom)

#check (AlgebraicNumbers.orderOf_complexConj :
  orderOf AlgebraicNumbers.complexConj = 2)

#check (AlgebraicNumbers.complexConjSubgroup_eq_fixingSubgroup :
  AlgebraicNumbers.complexConjSubgroup = AlgebraicNumbers.realIntersection.fixingSubgroup)

/- Example 65.14.7 (4): an algebraic extension of the rationals with a point of this
quotient is rationally isomorphic to the complex or real algebraic numbers. -/
@[stacks 02Z6] #check (AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.eq_algebraicQ_or_realIntersection :
    ∀ {k : Type} [Field k] [Algebra ℚ k] [Algebra.IsAlgebraic ℚ k],
      AlgebraicGeometry.Scheme.PreRelation.specToQuotientHom
        AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient.action
        (AlgebraicGeometry.FieldExtension.specMap ℚ k) →
      Nonempty (k ≃ₐ[ℚ] AlgebraicNumbers.algebraicQ) ∨
        Nonempty (k ≃ₐ[ℚ] AlgebraicNumbers.realIntersection))

