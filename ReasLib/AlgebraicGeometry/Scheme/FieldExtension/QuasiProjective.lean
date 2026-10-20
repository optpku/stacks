/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FieldExtension
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.Descent

/-!
# Quasi-projectivity and field extensions

This file records descent of quasi-projectivity along extensions of the ground field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.QuasiProjective

/-- Quasi-projectivity over a field descends along an arbitrary extension of the ground field. -/
theorem of_baseChangeToFieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (hXK : QuasiProjective (FieldExtension.toBase k K f)) :
    QuasiProjective f := sorry

end AlgebraicGeometry.QuasiProjective
