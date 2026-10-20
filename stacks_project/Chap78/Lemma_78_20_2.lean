/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.StructureMap
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace

/- Lemma 78.20.2 (1): there is a canonical `1`-morphism `π : 𝒮_U ⟶ [U/R]` of stacks in
groupoids over `(Sch/S)_fppf`. -/
@[stacks 044R] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fppfAtlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (stackInSets G.U.left).p (fppfQuotientStack G).p)

/- Lemma 78.20.2 (2): there is a canonical `1`-morphism `[U/R] ⟶ 𝒮_B` of stacks in
groupoids over `(Sch/S)_fppf`. -/
@[stacks 044R] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.toBase :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      CartesianBasedFunctor (fppfQuotientStack G).p (stackInSets B).p)

/- Lemma 78.20.2 (3): the composite `𝒮_U ⟶ 𝒮_B` is the `1`-morphism associated to the
structure morphism `U ⟶ B`. -/
@[stacks 044R] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.atlas_comp_toBase :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (fppfAtlas G).comp (toBase G) ≅ stackInSets.map G.U.hom)
