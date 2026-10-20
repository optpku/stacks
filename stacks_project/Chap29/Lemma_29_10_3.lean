/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyInjective.Separated
import StacksCheckRecall

/-!
# Lemma 29.10.3

Universally injective morphisms of schemes are separated.

@stack 05VE
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.10.3: A universally injective morphism is separated. -/
@[stacks 05VE] #check
  (@AlgebraicGeometry.universallyInjective_isSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.UniversallyInjective f], AlgebraicGeometry.IsSeparated f)
