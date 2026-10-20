/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Automorphic.ScalarExtension

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField

universe u v

/- The fixed-character Hecke operator is the linear endomorphism defined by its local finite sum. -/
#check (AlgebraicGeometry.SchemeOverField.CuspForms.heckeT :
  ∀ {k : Type u} [Field k] [Fintype k]
    {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)] {X : SchemeOverField k}
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    (character : closedPoints X.left → Λˣ) (place : closedPoints X.left),
    Module.End Λ (CuspForms X Λ character))
