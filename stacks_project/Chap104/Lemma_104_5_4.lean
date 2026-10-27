/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Colocalization
import StacksCheckRecall

/-!
# Lemma 104.5.4

For an algebraic stack `X` and `E` in `D_{LQCoh^{fbc}}(𝒪_X)`, there is a
canonical distinguished triangle `E' ⟶ E ⟶ P ⟶ E'⟦1⟧` in
`D_{LQCoh^{fbc}}(𝒪_X)` with `P` in `D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)` and
`Hom_{D(𝒪_X)}(E', P') = 0` for every such `P'`. The canonical `E'` is
`Lg_! g^* E` along the flat-fppf morphism of Lemma 103.14.2.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver CategoryTheory.Pretriangulated

universe u

/- Lemma 104.5.4: the canonical counit admits a distinguished completion with
parasitic third vertex; its source is left-orthogonal to parasitic-LQCoh objects,
and such completions are canonical up to unique isomorphism fixing E. -/
@[stacks 07BA]
#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.exists_colocalizationTriangle :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      (E : DerivedLQCohFbc X),
      ∃ (P : DerivedLQCohFbc X) (f : E ⟶ P)
        (δ : P ⟶ ((DerivedLQCohFbc.colocalize X).obj E)⟦(1 : ℤ)⟧),
        Triangle.mk ((DerivedLQCohFbc.colocalizeCounit X).app E) f δ ∈
            distTriang (DerivedLQCohFbc X) ∧
          derivedParasitic X P)

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.colocalize_hom_eq_zero :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      (E : DerivedLQCohFbc X),
      (DerivedCategory.cohomologyIn (FppfModules.parasiticLQCohFbc X)).leftOrthogonal
        ((DerivedLQCohFbc.inclusion X).obj ((DerivedLQCohFbc.colocalize X).obj E)))

#check (AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc.colocalizationTriangle_unique :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {E P P' : DerivedLQCohFbc X}
      {f : E ⟶ P} {δ : P ⟶ ((DerivedLQCohFbc.colocalize X).obj E)⟦(1 : ℤ)⟧}
      {f' : E ⟶ P'} {δ' : P' ⟶ ((DerivedLQCohFbc.colocalize X).obj E)⟦(1 : ℤ)⟧},
      Triangle.mk ((DerivedLQCohFbc.colocalizeCounit X).app E) f δ ∈
          distTriang (DerivedLQCohFbc X) →
      Triangle.mk ((DerivedLQCohFbc.colocalizeCounit X).app E) f' δ' ∈
          distTriang (DerivedLQCohFbc X) →
      derivedParasitic X P → derivedParasitic X P' →
      ∃! e : Triangle.mk ((DerivedLQCohFbc.colocalizeCounit X).app E) f δ ≅
          Triangle.mk ((DerivedLQCohFbc.colocalizeCounit X).app E) f' δ',
        e.hom.hom₂ = 𝟙 E)
