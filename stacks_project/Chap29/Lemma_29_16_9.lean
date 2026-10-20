/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.16.9: let `S` be a Jacobson scheme. Any scheme locally of finite type over `S` is
Jacobson. -/
@[stacks 02J5] #check (AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [JacobsonSpace S], JacobsonSpace X)
