/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 28.26.3: restriction of an ample invertible module to a closed subscheme is ample. -/
@[stacks 01PU] #check (AlgebraicGeometry.Scheme.Modules.IsAmple.pullback_of_isClosedImmersion :
    ∀ {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
      {L : X.Modules} [Invertible L],
      IsAmple L → IsAmple ((Scheme.Modules.pullback i).obj L))

end AlgebraicGeometry.Scheme.Modules
