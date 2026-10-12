/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import stacks_project.Chap88.«88_27_0_1»

/-!
# Completion is fully faithful on locally finite-type morphisms isomorphic over U

In the standing locally Noetherian setup, completing along `T` induces a
bijection on slice Hom-sets, so the completion functor is fully faithful.
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
  sorry

/-- Lemma 88.27.2 (1): in the standing locally Noetherian setup, if
`f : X' ⟶ X` is locally of finite type and an isomorphism over
`U = openComplementAlong X T`, and `g : Y ⟶ X` has `Y` locally Noetherian,
then completion defines a bijection
`Mor_X(Y, X') ⟶ Mor_{X_/T}(Y_/T, X'_/T)`, implemented as `Function.Bijective`
of `homMap T` on `Over.mk g ⟶ Over.mk f`. Here `Y_/T` is
`completionAlong Y (T.preimage (Points.continuous_map g))` and `f_/T` is
`map f T`. -/
@[stacks 0GDR]
theorem homMap_bijective {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (T : Closeds (Points X))
    (f : X' ⟶ X) [LocallyOfFiniteType f]
    [IsIso (openInverseImageTo f (openComplementι X T))] (g : Y ⟶ X) :
    Function.Bijective (fun (φ : Over.mk g ⟶ Over.mk f) ↦ homMap T φ) :=
  sorry

/-- Lemma 88.27.2 (2): in particular, the functor `functor X T` of
`completionFunctor` (88.27.0.1) is fully faithful: its map on Hom-sets of
`Source X T` is bijective. -/
@[stacks 0GDR]
theorem functor_map_bijective {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {Y Y' : Source X T} :
    Function.Bijective (fun (φ : Y ⟶ Y') ↦ (functor X T).map φ) :=
  sorry

/-- The completion functor `functor X T` is full. -/
instance instFull_functor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    (functor X T).Full :=
  sorry

/-- The completion functor `functor X T` is faithful. -/
instance instFaithful_functor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    (functor X T).Faithful :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
