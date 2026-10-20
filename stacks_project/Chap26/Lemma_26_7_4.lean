/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.7.4: the affine tilde counit is an isomorphism for every quasi-coherent module
sheaf. -/
@[stacks 01IA] #check Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
