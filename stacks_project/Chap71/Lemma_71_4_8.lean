/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Relative.BaseChange.Algebraic

/-!
# Lemma 71.4.8

Relative associated points of a quasi-coherent module on an algebraic space
are compatible with cartesian base change when the original morphism is
locally of finite type and the base change has residue-field transcendence
degree zero (in particular, when it is locally quasi-finite): the relative
assassin after pullback equals the preimage of the original relative assassin.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.4.8: for a cartesian square of algebraic spaces, a locally finite
   type morphism, and a quasi-coherent module, residue-field transcendence
   degree zero for the base change gives equality of the relative assassin
   after pullback with the inverse image of the original relative assassin. -/
@[stacks 0CV3] #check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.eq_preimage_of_residueFieldTrdegEq_zero :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'},
    ∀ [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    (hg : ∀ y' : Points Y', ResidueFieldTrdegEqAt g 0 y'),
    relativeAssassin f' ((pullback g').obj F) =
      Points.map g' ⁻¹' relativeAssassin f F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.eq_preimage_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'},
    ∀ [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    [AlgebraicSpace.LocallyQuasiFinite g],
    relativeAssassin f' ((pullback g').obj F) =
      Points.map g' ⁻¹' relativeAssassin f F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.mem_iff_map_mem_of_residueFieldTrdegEq_zero :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'},
    ∀ [AlgebraicSpace.LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (sq : IsPullback g' f' f g)
    (hg : ∀ y' : Points Y', ResidueFieldTrdegEqAt g 0 y') {x' : Points X'},
    x' ∈ relativeAssassin f' ((pullback g').obj F) ↔
      Points.map g' x' ∈ relativeAssassin f F)
