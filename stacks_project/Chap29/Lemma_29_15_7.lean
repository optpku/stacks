/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.LocallyOfFiniteType
import StacksCheckRecall

/-!
# Lemma 29.15.7

The reusable quasi-separatedness criterion is owned by
`ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.LocallyOfFiniteType`.

@stack 01T7
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.15.7: a morphism locally of finite type over a locally Noetherian scheme is
quasi-separated. -/
@[stacks 01T7] #check
  (AlgebraicGeometry.quasiSeparated_of_locallyOfFiniteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S],
      QuasiSeparated f)
