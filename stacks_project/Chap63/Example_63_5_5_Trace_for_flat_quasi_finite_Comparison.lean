/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.FiberLength

/-!
# Restriction of fibre weight along cartesian squares

For a cartesian base change of a flat, locally quasi-finite, locally finitely
presented morphism, the canonical fibre-weight function of the original
morphism restricts to the canonical fibre-weight function of the base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre-weight function of a cartesian base change of a flat, locally
quasi-finite, locally finitely presented morphism agrees with the restriction
of the original fibre weight. -/
theorem fiberWeight_isPullback {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [Flat f] [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
    [Flat f'] [LocallyQuasiFinite f'] [LocallyOfFinitePresentation f']
    (h_cart : IsPullback g' f' f g) :
    (fun x' : X' ↦ f.fiberWeight (g' x')) = f'.fiberWeight :=
  sorry

/-- Pointwise, the fibre weight of `f'` at `x'` equals the fibre weight of `f`
at `g' x'`. -/
theorem fiberWeight_isPullback_apply {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [Flat f] [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
    [Flat f'] [LocallyQuasiFinite f'] [LocallyOfFinitePresentation f']
    (h_cart : IsPullback g' f' f g) (x' : X') :
    f.fiberWeight (g' x') = f'.fiberWeight x' :=
  sorry

end AlgebraicGeometry.Scheme.Hom
