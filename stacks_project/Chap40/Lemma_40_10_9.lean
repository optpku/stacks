/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 40.10.9 (1): The arrow scheme of a groupoid scheme over a field spectrum is
equidimensional when its source and target maps are locally of finite type. -/
@[stacks 04LU] #check
  (AlgebraicGeometry.GroupoidScheme.equidimensionalSpaceArrow :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (uIso : G.U.left ≅ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.LocallyOfFiniteType G.t.left],
      EquidimensionalSpace G.R.left)

/- Lemma 40.10.9 (2): The dimension of the arrow scheme equals its local dimension at
every point. -/
@[stacks 04LU] #check
  (AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_eq_topologicalKrullDimAt :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (uIso : G.U.left ≅ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.LocallyOfFiniteType G.t.left] (r : G.R.left),
      topologicalKrullDim G.R.left = topologicalKrullDimAt r)

/- Lemma 40.10.9 (3): At every point of the arrow scheme, the two induced
`k`-scheme structures have the same base-field transcendence degree. -/
@[stacks 04LU] #check
  (AlgebraicGeometry.GroupoidScheme.source_residueFieldTrdegAt_eq_target :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (uIso : G.U.left ≅ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.LocallyOfFiniteType G.t.left] (r : G.R.left),
      AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt
          (AlgebraicGeometry.GroupoidScheme.arrowSourceOverField G uIso) r =
        AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt
          (AlgebraicGeometry.GroupoidScheme.arrowTargetOverField G uIso) r)

/- Lemma 40.10.9 (4): At a closed point of the arrow scheme, its dimension equals the
Krull dimension of the local ring. -/
@[stacks 04LU] #check
  (AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (uIso : G.U.left ≅ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.LocallyOfFiniteType G.t.left]
      (r : G.R.left) (h_r : IsClosed ({r} : Set G.R.left)),
      topologicalKrullDim G.R.left =
        ringKrullDim
          (AlgebraicGeometry.SchemeOverField.stalkRing
            (AlgebraicGeometry.GroupoidScheme.arrowSourceOverField G uIso) r))
