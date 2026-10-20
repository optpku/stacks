module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Map

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

#check (AlgebraicGeometry.AlgebraicSpace.mapsInto_comp_of_subset :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    {U : Over S} {x : X.functorOfPoints.obj (op U)}
    (hx : mapsInto (T : Set (Points X)) x),
    mapsInto (T' : Set (Points Y)) (f.app (op U) x))

namespace completionAlong

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.mapOfLe :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y))),
    completionAlong X T ⟶ completionAlong Y T')

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.mapOfLe_comp_ι :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y))),
    mapOfLe f T T' h ≫ ι Y T' = ι X T ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.mapOfLe_app :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) (T' : Closeds (Points Y))
    (h : Points.map f '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    (U : (Over S)ᵒᵖ) (x : (completionAlong X T).obj U),
    (ι Y T').app U ((mapOfLe f T T' h).app U x) =
      f.app U ((ι X T).app U x))

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
