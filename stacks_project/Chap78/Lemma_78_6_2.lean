/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_5_1_Group
public import stacks_project.Chap67.Lemma_67_38_5_Unramified
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

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

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 78.6.2 (1): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is locally of
finite type. Then `G.X.hom` is unramified if and only if it is unramified at
`AlgebraicSpace.Points.map η[G.X].left b` for every `b : AlgebraicSpace.Points B`. -/
@[stacks 0DSI]
theorem unramified_iff_unramifiedAt_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.Unramified G.X.hom ↔
      ∀ b : AlgebraicSpace.Points B,
        AlgebraicSpace.UnramifiedAt G.X.hom
          (AlgebraicSpace.Points.map η[G.X].left b) :=
  sorry

/-- Lemma 78.6.2 (2): let `S` be a scheme, let `B` be an algebraic space over `S`,
and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is locally of
finite type. Then `G.X.hom` is locally quasi-finite if and only if it is
quasi-finite at `AlgebraicSpace.Points.map η[G.X].left b` for every
`b : AlgebraicSpace.Points B`. -/
@[stacks 0DSI]
theorem locallyQuasiFinite_iff_quasiFiniteAt_one {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite G.X.hom ↔
      ∀ b : AlgebraicSpace.Points B,
        AlgebraicSpace.QuasiFiniteAt G.X.hom
          (AlgebraicSpace.Points.map η[G.X].left b) :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
