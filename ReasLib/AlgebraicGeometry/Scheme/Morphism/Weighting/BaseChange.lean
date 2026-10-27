/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberIntegral.BaseChange

/-!
# Weightings and base change

This module establishes that integer-valued weightings are preserved by
arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An integer-valued weighting of a locally quasi-finite scheme morphism pulls
back to a weighting after an arbitrary base change. -/
theorem IsWeighting.baseChange {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : f.IsWeighting w) (g : Y' ⟶ Y) :
    (pullback.snd f g).IsWeighting (fun x' ↦ w (pullback.fst f g x')) := sorry

variable {X Y X' Y' : Scheme.{u}}
variable {f : X ⟶ Y} [LocallyQuasiFinite f]
variable {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- A weighting of a locally quasi-finite morphism remains a weighting after
transport along an arbitrary cartesian square, with `w' = w ∘ g'`. -/
theorem IsWeighting.of_isPullback {w : X → ℤ} (hw : f.IsWeighting w)
    [LocallyQuasiFinite f'] (h_cart : IsPullback g' f' f g) :
    f'.IsWeighting (fun x' ↦ w (g' x')) := sorry

end AlgebraicGeometry.Scheme.Hom
