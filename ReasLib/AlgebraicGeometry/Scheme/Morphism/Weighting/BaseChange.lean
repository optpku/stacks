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

end AlgebraicGeometry.Scheme.Hom
