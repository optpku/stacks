/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree.Descent
import StacksCheckRecall

/-!
# Descent of universally bounded fibres

Universally bounded fibres of a morphism from a scheme to an algebraic space
descend along a representable morphism of algebraic spaces whose image of
points contains the image of the given morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.3.4: Let `S` be a scheme. Let `g : Y ⟶ X` be a representable morphism of
algebraic spaces over `S`. Let `f : U ⟶ X` be a morphism from a scheme towards `X`.
Let `f' : U ×_X Y ⟶ Y` be the base change of `f`. If
`Set.range (Points.map f) ⊆ Set.range (Points.map g)` and `f'` has universally
bounded fibres, then `f` has universally bounded fibres.

Representability of `g` makes the represented pullback `hg.pullback f` a scheme
over `S`, so the hypothesis applies to `hg.fst f : ofOver (hg.pullback f) ⟶ Y`. -/
@[stacks 03JO] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyBoundedFibres_of_range_subset_baseChange :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (g : Y ⟶ X)
    (hg : yoneda.relativelyRepresentable g) (f : ofOver U ⟶ X)
    (h_range : Set.range (Points.map f) ⊆ Set.range (Points.map g))
    (hf' : universallyBoundedFibres (hg.fst f)), universallyBoundedFibres f)

/- A fixed numerical bound on fibre degrees of the represented base change
`hg.fst f` also bounds the fibre degrees of `f`, under the image-inclusion
hypothesis `Set.range (Points.map f) ⊆ Set.range (Points.map g)`. -/
#check (AlgebraicGeometry.AlgebraicSpace.degreesOfFibresBoundedBy_of_range_subset_baseChange :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (g : Y ⟶ X)
    (hg : yoneda.relativelyRepresentable g) (f : ofOver U ⟶ X)
    (h_range : Set.range (Points.map f) ⊆ Set.range (Points.map g)) {n : ℕ}
    (hf' : degreesOfFibresBoundedBy (hg.fst f) n), degreesOfFibresBoundedBy f n)

/- Universal fibre boundedness of the scheme-apex projection `πY` implies the same
for `f`, when `πY` and `πU` exhibit a pullback square and
`Set.range (Points.map f) ⊆ Set.range (Points.map g)`. -/
#check (AlgebraicGeometry.AlgebraicSpace.universallyBoundedFibres_of_isPullback_of_range_subset :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U P : Over S} {g : Y ⟶ X} {f : ofOver U ⟶ X}
    {πY : ofOver P ⟶ Y} {πU : ofOver P ⟶ ofOver U} (sq : IsPullback πY πU g f)
    (h_range : Set.range (Points.map f) ⊆ Set.range (Points.map g))
    (hπY : universallyBoundedFibres πY), universallyBoundedFibres f)

end AlgebraicGeometry.AlgebraicSpace
