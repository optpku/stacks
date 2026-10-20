/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.LocalProperties
import StacksCheckRecall

/-!
# Unramified and locally quasi-finite group algebraic spaces

The structure morphism of a group algebraic space locally of finite type is
unramified (resp. locally quasi-finite) if and only if it is unramified
(resp. quasi-finite) at the identity-section point of every point of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

/- Lemma 78.6.2 (1): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is locally of
finite type. Then `G.X.hom` is unramified if and only if it is unramified at
`AlgebraicSpace.Points.map η[G.X].left b` for every `b : AlgebraicSpace.Points B`. -/
@[stacks 0DSI] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.unramified_iff_unramifiedAt_one :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      [AlgebraicSpace.LocallyOfFiniteType G.X.hom],
    AlgebraicSpace.Unramified G.X.hom ↔
      ∀ b : AlgebraicSpace.Points B,
        AlgebraicSpace.UnramifiedAt G.X.hom
          (AlgebraicSpace.Points.map η[G.X].left b))

/- Lemma 78.6.2 (2): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is locally of
finite type. Then `G.X.hom` is locally quasi-finite if and only if it is
quasi-finite at `AlgebraicSpace.Points.map η[G.X].left b` for every
`b : AlgebraicSpace.Points B`. -/
@[stacks 0DSI] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.locallyQuasiFinite_iff_quasiFiniteAt_one :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      [AlgebraicSpace.LocallyOfFiniteType G.X.hom],
    AlgebraicSpace.LocallyQuasiFinite G.X.hom ↔
      ∀ b : AlgebraicSpace.Points B,
        AlgebraicSpace.QuasiFiniteAt G.X.hom
          (AlgebraicSpace.Points.map η[G.X].left b))
