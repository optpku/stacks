/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.5.3: any immersion into a locally Noetherian scheme is quasi-compact. -/
@[stacks 01OX]
#check (AlgebraicGeometry.quasiCompact_of_isImmersion_of_isLocallyNoetherian :
  ∀ {Z X : Scheme.{u}} {f : Z ⟶ X} [IsImmersion f] [IsLocallyNoetherian X], QuasiCompact f)
