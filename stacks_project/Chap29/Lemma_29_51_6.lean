module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.DenseOpen
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 29.51.6: a birational morphism between schemes with finitely many irreducible
components becomes an isomorphism over a dense open of the target if it is quasi-compact or
separated and satisfies the stated finite-type alternative. -/
@[stacks 0BAJ] #check
  (AlgebraicGeometry.IsBirational.exists_dense_open_isIso_restrict :
    ∀ {X Y : Scheme.{u}}
      [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
      (f : X ⟶ Y) [IsBirational f],
      (QuasiCompact f ∨ IsSeparated f) →
        ((LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) →
          ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsIso (f ∣_ V))
