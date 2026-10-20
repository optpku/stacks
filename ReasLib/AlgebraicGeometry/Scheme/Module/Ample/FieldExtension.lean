/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Ample invertible modules and field extensions

This file records descent of the existence of an ample invertible module from a field-extension
base change.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule

/-- If the base change of a scheme to an arbitrary field extension admits an ample invertible
module, then the original scheme admits one. -/
theorem of_baseChangeToFieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : HasAmpleInvertibleModule (AlgebraicGeometry.FieldExtension.baseChange k K f)) :
    HasAmpleInvertibleModule X := sorry

end AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule
