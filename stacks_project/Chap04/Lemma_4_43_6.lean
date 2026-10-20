/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X Y : C) [ExactPairing X Y]

/- The source needs two Hom-set equivalences natural in both `Z` and `Z'`, under Definition
4.43.5's fixed-pair owner `ExactPairing X Y`. The pointwise candidates `tensorRightHomEquiv` and
`tensorLeftHomEquiv` have separate naturality lemmas, whereas `tensorRightAdjunction X Y` and
`tensorLeftAdjunction X Y` package exactly those equivalences with both-variable functoriality.
The adjunction owners therefore give the cleaner reusable surface. There is no generalization:
specializing their pairing parameters to `X` and `Y` recovers the two displayed bijections, while
downstream code retains the standard adjunction and pointwise Hom-equivalence APIs. -/

/- Lemma 4.43.6 (1): if `Y` is a left dual of `X`, represented by `ExactPairing X Y`, then
`Mor (Z' ⊗ X, Z) ≃ Mor (Z', Z ⊗ Y)` functorially in `Z` and `Z'`. -/
@[stacks 0FFQ "right-tensor Hom equivalence, natural in source and target"]
#check (tensorRightAdjunction X Y : tensorRight X ⊣ tensorRight Y)

/- Lemma 4.43.6 (2): if `Y` is a left dual of `X`, represented by `ExactPairing X Y`, then
`Mor (Y ⊗ Z', Z) ≃ Mor (Z', X ⊗ Z)` functorially in `Z` and `Z'`. -/
@[stacks 0FFQ "left-tensor Hom equivalence, natural in source and target"]
#check (tensorLeftAdjunction X Y : tensorLeft Y ⊣ tensorLeft X)

end CategoryTheory
