/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ShortExact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.119.3

Naturality of the determinant comparison under an isomorphism of finite-projective short exact
rows is part of the canonical bundled short-complex API.

@stack 0FJC
-/

/- Lemma 15.119.3: an isomorphism of finite-projective short exact rows intertwines their
determinant comparison maps. -/
@[stacks 0FJC "Lemma 15.119.3: determinant comparison naturality"]
#check @CategoryTheory.ShortComplex.ShortExact.determinantTensorIso_naturality_apply

#check @CategoryTheory.ShortComplex.ShortExact.determinantTensorIso
#check @CategoryTheory.ShortComplex.ShortExact.determinantTensorIso_spec
#check @Module.Determinant.mapIso

end
