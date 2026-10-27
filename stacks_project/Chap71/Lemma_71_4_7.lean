/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 71.4.7

Relative associated points of a quasi-coherent module on an algebraic space
are compatible with cartesian base change when the original morphism is
locally of finite type: the relative assassin after pullback is contained in
the preimage of the original relative assassin, and relatively associated
points lift through any compatible point of the base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.4.7 (1): let `S` be a scheme and let `IsPullback g' f' f g` be a
cartesian square of algebraic spaces over `S`. Let `F` be a quasi-coherent
`𝒪_X`-module. If `f` is locally of finite type, then
`relativeAssassin f' ((pullback g').obj F)` is contained in the preimage of
`relativeAssassin f F` under `Points.map g'`. -/
@[stacks 0CV2] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.subset_preimage :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      [AlgebraicSpace.LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g),
      relativeAssassin f' ((pullback g').obj F) ⊆
        Points.map g' ⁻¹' relativeAssassin f F)

/- If a point of `X'` is relatively associated after cartesian base change,
then its image in `X` is relatively associated. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.mem_map_of_mem :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      [AlgebraicSpace.LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
      {x' : Points X'} (hx' : x' ∈ relativeAssassin f' ((pullback g').obj F)),
      Points.map g' x' ∈ relativeAssassin f F)

/- Lemma 71.4.7 (2): with the same cartesian square, locally-of-finite-type
hypothesis, and quasi-coherent module `F`, if `x` lies in
`relativeAssassin f F` and `y'` is a point of `Y'` with
`Points.map f x = Points.map g y'`, then there exists a point `x'` in
`relativeAssassin f' ((pullback g').obj F)` with `Points.map g' x' = x` and
`Points.map f' x' = y'`. -/
@[stacks 0CV2] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.exists_of_mem_map_eq :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      [AlgebraicSpace.LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
      {x : Points X} {y' : Points Y'} (hx : x ∈ relativeAssassin f F)
      (hxy : Points.map f x = Points.map g y'),
      ∃ x' : Points X',
        x' ∈ relativeAssassin f' ((pullback g').obj F) ∧
          Points.map g' x' = x ∧ Points.map f' x' = y')
