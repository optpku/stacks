/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The quotient spectrum morphism is locally of finite presentation exactly when
its defining ideal is finitely generated. -/
theorem locallyOfFinitePresentation_spec_quotient_iff {A : Type u} [CommRing A]
    (I : Ideal A) :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ↔ I.FG :=
  sorry

end AlgebraicGeometry
