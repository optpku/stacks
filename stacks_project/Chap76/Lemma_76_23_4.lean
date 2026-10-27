/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Fiberwise
import StacksCheckRecall

/-!
# Flatness of a morphism of algebraic spaces from fibrewise flatness

In a triangle `X ⟶ Y ⟶ Z` of algebraic spaces, if `X` is locally of finite
presentation and flat over `Z`, `Y` is locally of finite type over `Z`, and
every fibre of `X` over a point of `|Z|` is flat over the corresponding fibre
of `Y`, then `X ⟶ Y` is flat. If that morphism is also surjective, then `Y`
is flat over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.23.4 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `X` is locally of finite
presentation over `Z`, `X` is flat over `Z`, for every `z : Points Z` the
fibre of `X` over `z` is flat over the fibre of `Y` over `z` in the sense of
`fiberFlatOver f h z`, and `Y` is locally of finite type over `Z`. Then `f`
is flat. -/
@[stacks 05X1]
#check (AlgebraicGeometry.AlgebraicSpace.Flat.of_fiberFlatOver :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
      [Flat (f ≫ h)] [LocallyOfFiniteType h],
      (∀ z : Points Z, fiberFlatOver f h z) → Flat f)

/- Lemma 76.23.4 (2): Let `S` be a scheme. Let `f : X ⟶ Y` and `h : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `X` is locally of finite
presentation over `Z`, `X` is flat over `Z`, for every `z : Points Z` one has
`fiberFlatOver f h z`, and `Y` is locally of finite type over `Z`. If `f` is
also surjective, then `Y` is flat over `Z`. -/
@[stacks 05X1]
#check (AlgebraicGeometry.AlgebraicSpace.Flat.base_of_fiberFlatOver_of_surjective :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
      [Flat (f ≫ h)] [LocallyOfFiniteType h] [Surjective f],
      (∀ z : Points Z, fiberFlatOver f h z) → Flat h)

end AlgebraicGeometry.AlgebraicSpace
