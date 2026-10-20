/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Jacobson
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry Cardinal
open scoped AlgebraicGeometry

universe u

/- Lemma 33.14.2 (1): after a sufficiently large field extension, the residue field of every
closed point of the base change is algebraic over the extended base field. -/
@[stacks 0479] #check
  (AlgebraicGeometry.FieldExtension.exists_cardinal_residueField_isAlgebraic_of_closedPoint :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      ∃ κ : Cardinal.{u}, ∀ {K : Type u} [Field K] [Algebra k K],
        κ < #K →
          ∀ x : AlgebraicGeometry.FieldExtension.baseChange k K f,
            x ∈ closedPoints (AlgebraicGeometry.FieldExtension.baseChange k K f) →
              Scheme.Hom.ResidueField.IsAlgebraicOverSpec
                (AlgebraicGeometry.FieldExtension.toBase k K f) x)

/- Lemma 33.14.2 (2): after a sufficiently large field extension, the base change is a Jacobson
scheme. -/
@[stacks 0479] #check
  (AlgebraicGeometry.FieldExtension.exists_cardinal_jacobsonSpace :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      ∃ κ : Cardinal.{u}, ∀ {K : Type u} [Field K] [Algebra k K],
        κ < #K →
          JacobsonSpace (AlgebraicGeometry.FieldExtension.baseChange k K f))
