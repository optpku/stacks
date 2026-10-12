/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.9.3: for an extension of algebraically closed fields and a proper
scheme over the base field, finite étale schemes are preserved by scalar extension
through an equivalence of categories. -/
@[stacks 0A49] #check
  (AlgebraicGeometry.SchemeOverField.finiteEtaleBaseChangeIsEquivalenceOfAlgClosed :
    ∀ {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [Algebra k k']
      [IsAlgClosed k'] (X : SchemeOverField k) [IsProper X.hom],
    Functor.IsEquivalence
      (Scheme.finiteEtaleBaseChange (FieldExtension.toSource k k' X.hom)))
