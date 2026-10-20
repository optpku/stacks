/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Finite presentation of affine spectrum morphisms

This file records the finite-presentation property of the spectrum morphism induced by a
finitely presented algebra.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The spectrum morphism induced by a finitely presented algebra is of finite presentation. -/
theorem finitePresentation_specMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] :
    FinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B))) := sorry

end AlgebraicGeometry.Scheme.Hom
