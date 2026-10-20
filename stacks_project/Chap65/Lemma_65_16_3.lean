/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence
public import stacks_project.Chap65.Lemma_65_16_3_Equivalence

/-!
# Lemma 65.16.3

Change of base scheme as an equivalence between algebraic spaces over `S` and
algebraic spaces over `S'` equipped with a morphism to `S`.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 65.16.3: a morphism of base schemes induces an equivalence between algebraic
spaces over the smaller base and algebraic spaces over the larger base equipped with
a morphism to the smaller base. The forward functor sends `F` to
`Over.mk (AlgebraicGeometry.AlgebraicSpace.extendBaseHom g F)`. -/
@[stacks 04SG] #check (AlgebraicGeometry.AlgebraicSpace.extendBaseEquivalence :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S'),
    AlgebraicSpace S ≌ Over (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk g)))
