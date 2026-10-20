/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism

/-!
# Unique factorization of monomorphic field-valued points

Two monomorphisms `Spec(k) ⟶ X` from spectra of fields that represent the same
point of `|X|` factor uniquely through each other.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

open AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.iso_unique_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
      [Mono p.hom] [Mono q.hom],
      Points.mk p = Points.mk q →
        Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q))
