/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Surjectivity and reductions of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

/-- A morphism of formal algebraic spaces representable by algebraic spaces has
surjective scheme pullback projections if and only if its induced morphism
between reductions is surjective. -/
theorem surjective_pullback_iff {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) {f : X ⟶ Y}
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hf.pullbackHom ξ)) ↔
      AlgebraicSpace.Surjective (RX.map RY f) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData
