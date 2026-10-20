/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

/- Example 78.7.1 (Multiplicative group algebraic space) (1): the multiplicative group over
`B` is a group algebraic space in the slice `Over B`. -/
@[stacks 043J] #check
  (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.groupSpace :
    {S : Scheme.{u}} → (B : AlgebraicSpace S) → GroupAlgebraicSpace B)

/- Example 78.7.1 (Multiplicative group algebraic space) (2): its functor of points is the
product describing `B ×_S 𝔾ₘ[S]`. -/
@[stacks 043J] #check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.space_functorOfPoints :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    (space B).functorOfPoints = (B.functorOfPoints ⨯ (ofScheme S).functorOfPoints))

/- Example 78.7.1 (Multiplicative group algebraic space) (3): morphisms over `B` from a scheme `T`
to `asOver B` are the group of global units `Γ(T.left, ⊤)ˣ`. -/
@[stacks 043J] #check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.homOverMulEquiv :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} → {T : Over S} →
    (t : ofOver T ⟶ B) → (Over.mk t ⟶ asOver B) ≃* Γ(T.left, ⊤)ˣ)

/- Example 78.7.1 (Multiplicative group algebraic space) (4): this equivalence is natural in
scheme-valued test objects over `B`, with pullback on global units. -/
@[stacks 043J] #check (AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup.homOverMulEquiv_comp :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {T T' : Over S}
    (map : T ⟶ T') (t : ofOver T ⟶ B) (t' : ofOver T' ⟶ B)
    (ht : yoneda.map map ≫ t' = t) (point : Over.mk t' ⟶ asOver B),
    homOverMulEquiv t (Over.homMk (V := Over.mk t') (yoneda.map map) ht ≫ point) =
      (AlgebraicGeometry.MultiplicativeGroup.points S).map map.op (homOverMulEquiv t' point))

/- Example 78.7.1 (Multiplicative group algebraic space) (5): here `𝔾ₘ[S]` is the multiplicative
group scheme over `S`. -/
@[stacks 043J] #check
  (AlgebraicGeometry.MultiplicativeGroup.baseChange : (S : Scheme.{u}) → CommGrp (Over S))
