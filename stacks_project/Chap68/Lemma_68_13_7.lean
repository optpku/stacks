/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace.Field
import StacksCheckRecall

/-!
# Residual spaces isomorphic to spectra of fields

A residual space of an algebraic space at a point is isomorphic to the spectrum
of a field if and only if the point is represented by a monomorphism from such
a spectrum. On a decent algebraic space this holds at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.13.7: A residual space at a point is isomorphic to the spectrum of
a field if and only if the point has a monomorphic field-valued representative. -/
@[stacks 0H1R] #check
  (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_iso_spec_iff_existsMonoFieldValuedPoint :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} {x : Points X}
      (ι : Z ⟶ X) [IsResidualSpace ι x],
      (∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
          Nonempty (Z ≅ ofOver (Over.mk σ))) ↔
        existsMonoFieldValuedPoint X x)

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_iso_spec_of_isDecent :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsDecent X] {x : Points X}
    (ι : Z ⟶ X) [IsResidualSpace ι x],
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
      Nonempty (Z ≅ ofOver (Over.mk σ)))
