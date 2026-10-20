/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of completion along a closed subspace

A morphism of algebraic spaces induces a cartesian square of completions along
a closed subspace and its inverse image. The induced map of completions is
representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a section of `X'` fppf-locally factors through an infinitesimal
neighbourhood of the inverse image of `i` along `f : X' ⟶ X`, then
postcomposition with `f` fppf-locally factors through an infinitesimal
neighbourhood of `i`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_comp {S : Scheme.{u}}
    {X' X Z : AlgebraicSpace S} (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} {x : X'.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood (inverseImageι f i) x) :
    fppfLocallyFactorsThroughNeighbourhood i (f.app U x) :=
  sorry

namespace completionAlongSubspace

/-- The morphism of completions induced by `f : X' ⟶ X` along the inverse image
closed subspace `Z' = f⁻¹(Z)` given by `inverseImageι f i`. -/
def map {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    completionAlongSubspace (inverseImageι f i) ⟶ completionAlongSubspace i where
  app U :=
    ofHom fun x ↦
      ⟨f.app U x.1, fppfLocallyFactorsThroughNeighbourhood_comp f i x.property⟩
  naturality := sorry

/-- The underlying section of `map f i` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ)
    (x : (completionAlongSubspace (inverseImageι f i)).obj U) :
    (ι i).app U ((map f i).app U x) =
      f.app U ((ι (inverseImageι f i)).app U x) :=
  sorry

/-- The square of completions along a closed subspace and its inverse image
commutes. -/
theorem map_comp_ι {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    map f i ≫ ι i = ι (inverseImageι f i) ≫ f :=
  sorry

end completionAlongSubspace

/-- For a morphism `f : X' ⟶ X` of algebraic spaces over a scheme `S` and a
closed immersion `i : Z ⟶ X`, completion along the inverse image
`inverseImageι f i` forms a cartesian square with `f` and the completion
inclusion along `i` in `(Over S)ᵒᵖ ⥤ Type u`. -/
@[stacks 0GXV]
theorem completionAlongSubspace_isPullback {S : Scheme.{u}} {X' X Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsPullback (completionAlongSubspace.ι (inverseImageι f i))
      (completionAlongSubspace.map f i) f (completionAlongSubspace.ι i) :=
  sorry

/-- The morphism of completions along a closed subspace and its inverse image
induced by a morphism of algebraic spaces is representable by algebraic spaces. -/
@[stacks 0GXV]
theorem representableByAlgebraicSpaces_completionAlongSubspace_map
    {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    representableByAlgebraicSpaces (completionAlongSubspace.map f i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
