/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.24.3 (1): immersions are closed under composition. -/
@[stacks 02V0] #check IsImmersion.comp

/- Lemma 26.24.3 (2): closed immersions are closed under composition. -/
@[stacks 02V0] #check IsClosedImmersion.comp

/- Lemma 26.24.3 (3): open immersions are closed under composition. -/
@[stacks 02V0] #check IsOpenImmersion.comp
