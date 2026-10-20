module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.Descent

/-!
# Descent of universally bounded fibres

Fibre-degree bounds for morphisms from schemes to algebraic spaces descend
along representable morphisms whose images contain the image of the given morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A fixed numerical bound on fibre degrees of the represented base change
`hg.fst f` also bounds the fibre degrees of `f`, under the image-inclusion
hypothesis `Set.range (Points.map f) ⊆ Set.range (Points.map g)`. -/
theorem degreesOfFibresBoundedBy_of_range_subset_baseChange {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (g : Y ⟶ X)
    (hg : yoneda.relativelyRepresentable g) (f : ofOver U ⟶ X)
    (h_range : Set.range (Points.map f) ⊆ Set.range (Points.map g)) {n : ℕ}
    (hf' : degreesOfFibresBoundedBy (hg.fst f) n) : degreesOfFibresBoundedBy f n :=
  sorry

/-- Universal fibre boundedness descends from the represented base change along a
representable morphism whose image on points contains the image of the given morphism. -/
theorem universallyBoundedFibres_of_range_subset_baseChange {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (g : Y ⟶ X)
    (hg : yoneda.relativelyRepresentable g) (f : ofOver U ⟶ X)
    (h_range : Set.range (Points.map f) ⊆ Set.range (Points.map g))
    (hf' : universallyBoundedFibres (hg.fst f)) : universallyBoundedFibres f :=
  sorry

/-- Universal fibre boundedness of the scheme-apex projection `πY` implies the same
for `f`, when `πY` and `πU` exhibit a pullback square and
`Set.range (Points.map f) ⊆ Set.range (Points.map g)`. -/
theorem universallyBoundedFibres_of_isPullback_of_range_subset {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U P : Over S} {g : Y ⟶ X} {f : ofOver U ⟶ X}
    {πY : ofOver P ⟶ Y} {πU : ofOver P ⟶ ofOver U} (sq : IsPullback πY πU g f)
    (h_range : Set.range (Points.map f) ⊆ Set.range (Points.map g))
    (hπY : universallyBoundedFibres πY) : universallyBoundedFibres f :=
  sorry

/-- A fixed numerical bound on fibre degrees of `ofOverMap f ≫ h` also bounds
the fibre degrees of `h`, when `f.left` is flat and surjective. -/
theorem degreesOfFibresBoundedBy_of_comp_of_flat_of_surjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : U ⟶ V) (h : ofOver V ⟶ X)
    [AlgebraicGeometry.Flat f.left] [AlgebraicGeometry.Surjective f.left]
    {n : ℕ} (hg : degreesOfFibresBoundedBy (ofOverMap f ≫ h) n) :
    degreesOfFibresBoundedBy h n :=
  sorry

/-- Universal fibre boundedness of a morphism from a scheme to an algebraic space
descends along flat surjective precomposition by a morphism of schemes over `S`. -/
theorem universallyBoundedFibres_of_comp_of_flat_of_surjective
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U V : Over S}
    (f : U ⟶ V) (h : ofOver V ⟶ X)
    [AlgebraicGeometry.Flat f.left] [AlgebraicGeometry.Surjective f.left]
    (hg : universallyBoundedFibres (ofOverMap f ≫ h)) :
    universallyBoundedFibres h :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
