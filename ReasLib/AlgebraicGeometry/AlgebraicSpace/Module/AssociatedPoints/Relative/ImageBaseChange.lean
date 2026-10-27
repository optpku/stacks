/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Image containment of relative associated points under base change

Relative associated points of a quasi-coherent module on an algebraic space
that are covered by a morphism remain covered after arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- For a locally-of-finite-type morphism `f : X ⟶ Y` and a quasi-coherent
module `F` on `X`, containment of `relativeAssassin f F` in the image of
`g : X' ⟶ X` persists after every base change `h : Z ⟶ Y`.
The base-changed source of `g` is represented by `X_Z ×_X X'`. -/
@[stacks 0CW2]
theorem subset_range_afterBaseChange {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] (hAss : relativeAssassin f F ⊆ Set.range (Points.map g))
    {Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    relativeAssassin (Limits.pullback.snd f h) ((pullback (Limits.pullback.fst f h)).obj F) ⊆
      Set.range (Points.map (Limits.pullback.fst (Limits.pullback.fst f h) g)) :=
  sorry

/-- If a point of `|X_Z|` is relatively associated after base change along
`h : Z ⟶ Y`, then it lies in the image of `|g_Z|`. -/
theorem mem_range_afterBaseChange {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] (hAss : relativeAssassin f F ⊆ Set.range (Points.map g))
    {Z : AlgebraicSpace S} (h : Z ⟶ Y) {x : Points (Limits.pullback f h)}
    (hx : x ∈ relativeAssassin (Limits.pullback.snd f h)
      ((pullback (Limits.pullback.fst f h)).obj F)) :
    x ∈ Set.range (Points.map (Limits.pullback.fst (Limits.pullback.fst f h) g)) :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
