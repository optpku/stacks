/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.OpenBaseChange

/-!
# Dominance after extending the ground field

Dominance of a morphism between schemes over a field spectrum is invariant under extension of
the ground field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsDominant

/-- A morphism of schemes over `Spec k` is dominant if and only if its base change along a field
extension `E/k` is dominant. -/
theorem iff_fieldExtension
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    IsDominant f.left ↔
      IsDominant (((FieldExtension.Over.functor k E).map f).left) := sorry

end AlgebraicGeometry.IsDominant
