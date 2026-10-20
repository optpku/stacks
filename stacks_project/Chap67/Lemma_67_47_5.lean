/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Gluing
import StacksCheckRecall

/-!
# Lemma 67.47.5

A rational map from a reduced algebraic space to a separated algebraic space
is represented by a unique morphism on its domain of definition.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.47.5 (1): a rational map from a reduced algebraic space `X` to a
separated algebraic space `Y` over a scheme `S` is represented by the
canonical morphism on its domain of definition `U ⊂ X`. -/
@[stacks 0EMR] #check
  (AlgebraicGeometry.AlgebraicSpace.RationalMap.toRationalMap_toPartialMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y),
      φ.toPartialMap.toRationalMap = φ)

/- Lemma 67.47.5 (2): a morphism on the domain of definition of a rational map
from a reduced algebraic space to a separated algebraic space that represents
that rational map equals the canonical representing morphism. -/
@[stacks 0EMR] #check (AlgebraicGeometry.AlgebraicSpace.RationalMap.eq_toPartialMap_hom_of_toRationalMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsReduced X] [IsSeparated Y] (φ : RationalMap X Y)
    (f : φ.domainSite.left ⟶ Y)
    (hf : (⟨φ.domainSite, RationalMap.dense_domainSite φ, f⟩ : PartialMap X Y).toRationalMap = φ),
    f = φ.toPartialMap.hom)
