/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits

universe u

/- Lemma 29.15.4 (1): the base change of a morphism which is locally of finite type is locally of
finite type. -/
@[stacks 01T4] #check
  (AlgebraicGeometry.LocallyOfFiniteType.pullback_snd :
    ∀ {X S S' : Scheme.{u}} {f : X ⟶ S},
      LocallyOfFiniteType f → ∀ g : S' ⟶ S, LocallyOfFiniteType (pullback.snd f g))

/- Lemma 29.15.4 (2): the base change of a morphism of finite type is of finite type. -/
@[stacks 01T4] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.pullback_snd :
    ∀ {X S S' : Scheme.{u}} {f : X ⟶ S},
      Scheme.Hom.FiniteType f → ∀ g : S' ⟶ S, Scheme.Hom.FiniteType (pullback.snd f g))
