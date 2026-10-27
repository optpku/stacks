/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cartesian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The terminal map of a smooth scheme over a field is smooth. -/
instance instSmooth_terminalFrom (X : SchemeOverField k) [Smooth X.hom] :
    Smooth (terminal.from X).left := sorry

/-- The terminal map preserves the relative dimension over the field. -/
instance instRelativeDimension_terminalFrom (X : SchemeOverField k) (d : ℕ)
    [RelativeDimension X.hom d] :
    RelativeDimension (terminal.from X).left d := sorry

/-- The first product projection is smooth when its second factor is smooth over the field. -/
instance instSmooth_prodFst (X Y : SchemeOverField k) [Smooth Y.hom] :
    Smooth (prod.fst : X ⨯ Y ⟶ X).left := sorry

/-- The first product projection has the relative dimension of its second factor. -/
instance instRelativeDimension_prodFst (X Y : SchemeOverField k) (d : ℕ)
    [RelativeDimension Y.hom d] :
    RelativeDimension (prod.fst : X ⨯ Y ⟶ X).left d := sorry

end AlgebraicGeometry.SchemeOverField
