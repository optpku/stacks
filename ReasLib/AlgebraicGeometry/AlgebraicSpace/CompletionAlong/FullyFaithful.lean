module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor

/-!
# Full faithfulness of completion along a closed subset

Over a locally Noetherian algebraic space, completion induces a bijection on
morphisms from locally Noetherian spaces to locally finite-type spaces that
are isomorphic over the open complement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- The morphism of completions over `X_/T` induced by a morphism in `Over X`. -/
def homMap {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') :
    Over.mk (map Y.hom T) ⟶ Over.mk (map Y'.hom T) :=
  Over.homMk (mapOver T φ) (mapOver_comp_map T φ)

/-- The underlying morphism of `homMap T φ` is `mapOver T φ`. -/
theorem homMap_left {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') :
    (homMap T φ).left = mapOver T φ :=
  rfl

/-- Over a locally Noetherian algebraic space, completion along a closed subset
induces a bijection on morphisms from a locally Noetherian space to a locally
finite-type space that is isomorphic over the open complement. -/
theorem homMap_bijective {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (T : Closeds (Points X))
    (f : X' ⟶ X) [LocallyOfFiniteType f]
    [IsIso (openInverseImageTo f (openComplementι X T))] (g : Y ⟶ X) :
    Function.Bijective (fun (φ : Over.mk g ⟶ Over.mk f) ↦ homMap T φ) :=
  sorry

/-- Completion along a closed subset of a locally Noetherian algebraic space
is bijective on Hom-sets of locally finite-type morphisms that are isomorphic
over the open complement. -/
theorem functor_map_bijective {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {Y Y' : Source X T} :
    Function.Bijective (fun (φ : Y ⟶ Y') ↦ (completionFunctor X T).map φ) :=
  sorry

/-- Completion along a closed subset of a locally Noetherian algebraic space
is full on locally finite-type morphisms isomorphic over the open complement. -/
instance instFull_functor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    (completionFunctor X T).Full where
  map_surjective := (functor_map_bijective X T).surjective

/-- Completion along a closed subset of a locally Noetherian algebraic space
is faithful on locally finite-type morphisms isomorphic over the open complement. -/
instance instFaithful_functor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    (completionFunctor X T).Faithful where
  map_injective h := (functor_map_bijective X T).injective h

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
