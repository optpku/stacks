/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.25.9: if `f : X ⟶ S` is a flat morphism of schemes, then generalizations lift along
`f`. Equivalently, the underlying map of topological spaces of a flat morphism of schemes is a
generalizing map in the sense of Topology, Definition 5.19.4. -/
@[stacks 03HV] #check (AlgebraicGeometry.Flat.generalizingMap :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Flat f],
    GeneralizingMap f)
