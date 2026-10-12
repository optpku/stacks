/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat CategoryTheory Limits

universe u

/- Lemma 33.8.2: for a scheme `X` over a field `k` and a field extension `K / k`,
`X` is geometrically irreducible over `k` if and only if its field-extension base change is
geometrically irreducible over `K`. -/
@[stacks 054P] #check
  (AlgebraicGeometry.GeometricallyIrreducible.BaseChange.iff_fieldExtension :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      {K : Type u} [Field K] [Algebra k K],
      GeometricallyIrreducible f ↔
        GeometricallyIrreducible (FieldExtension.toBase k K f))
