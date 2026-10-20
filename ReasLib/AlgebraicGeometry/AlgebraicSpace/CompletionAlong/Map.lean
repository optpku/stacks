/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong

/-!
# Morphisms of completions along closed subsets

A morphism of algebraic spaces sending a closed subset `T` into a closed subset
`T'` induces a morphism of completions `completionAlong X T ⟶ completionAlong Y T'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a Yoneda section of `X` maps into `T` and `Points.map f` sends `T` into
`T'`, then the postcomposition with `f` maps into `T'`. -/
theorem mapsInto_comp_of_subset {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    {U : Over S} {x : X.functorOfPoints.obj (op U)}
    (hx : mapsInto (T : Set (Points X)) x) :
    mapsInto (T' : Set (Points Y)) (f.app (op U) x) :=
  sorry

namespace completionAlong

/-- The morphism of completions induced by `f : X ⟶ Y` when
`Points.map f` sends `T` into `T'`. -/
def mapOfLe {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y))) :
    completionAlong X T ⟶ completionAlong Y T' where
  app U := ofHom fun x ↦ ⟨f.app U x.1, mapsInto_comp_of_subset f T T' h x.2⟩
  naturality := sorry

/-- Postcomposing `mapOfLe f T T' h` with `ι Y T'` recovers `ι X T ≫ f`. -/
theorem mapOfLe_comp_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y))) :
    mapOfLe f T T' h ≫ ι Y T' = ι X T ≫ f :=
  sorry

/-- The underlying section of `mapOfLe f T T' h` is the component of `f`. -/
theorem mapOfLe_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    (U : (Over S)ᵒᵖ) (x : (completionAlong X T).obj U) :
    (ι Y T').app U ((mapOfLe f T T' h).app U x) =
      f.app U ((ι X T).app U x) :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
