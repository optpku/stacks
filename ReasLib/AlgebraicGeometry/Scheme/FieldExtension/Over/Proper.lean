/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Over

/-- Properness is preserved by the canonical base change of a scheme over a field. -/
instance instIsProperBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [IsProper X.hom] :
    IsProper (baseChange k K X).hom := sorry

end AlgebraicGeometry.FieldExtension.Over
