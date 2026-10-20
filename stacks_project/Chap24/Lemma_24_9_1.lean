/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Graded.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.9.1

The reusable owner works for an arbitrary grading type and exposes the degreewise module
pullback-pushforward adjunction itself.  Its Hom equivalence specializes to the bijection in the
source.
-/

/- Lemma 24.9.1 (0FR8): pullback and pushforward of graded module sheaves are related degreewise
by the module pullback-pushforward adjunction. -/
@[stacks 0FR8 "graded module pullback-pushforward adjunction"]
#check @RingedSite.Hom.Graded.adjunction

#check @RingedSite.Hom.Graded.homEquiv
