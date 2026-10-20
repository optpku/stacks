/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Proper
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison

/-!
# Projective morphisms and field extensions

This file records descent of projectivity along extensions of the ground field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Projective

/-- Projectivity over a field descends along an arbitrary extension of the ground field. -/
theorem of_baseChangeToFieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (hXK : Projective (FieldExtension.toBase k K f)) :
    Projective f := sorry

end AlgebraicGeometry.Projective
