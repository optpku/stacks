/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Flat.Lifting
import StacksCheckRecall

/-!
# Lemma 10.81.3

@stack 058F

Flatness is expressed by surjectivity on `Hom` from every finitely presented
test module. The chapter recalls the shared lifting criterion directly.
-/

@[expose] public section

/- Lemma 10.81.3: an `R`-module `M` is flat if and only if for every finitely presented
`R`-module `P` and every surjective linear map `N → M`, postcomposition induces a surjection
`Hom_R(P, N) → Hom_R(P, M)`. -/
@[stacks 058F "source Hom-surjectivity criterion"]
#check @Module.Flat.iff_postcomp_surjective_finitePresentation
