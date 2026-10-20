/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.Field.JacobiZariski

/-!
# Jacobi-Zariski for towers of fields

This file recalls the canonical exact sequence for a tower of fields.

@stack 07E2
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace Algebra

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/- Lemma 15.34.2 (1), tag `07E2`: the left edge
`M ⊗[L] H1Cotangent K L ⟶ H1Cotangent K M` is injective. -/
@[stacks 07E2 "Lemma 15.34.2 (1)"]
#check @H1Cotangent.liftBaseChange_map_injective

/- Lemma 15.34.2 (2), tag `07E2`:
`H1Cotangent K M ⟶ H1Cotangent L M ⟶ M ⊗[L] Ω[L⁄K]` is exact. -/
@[stacks 07E2 "Lemma 15.34.2 (2)"]
#check @H1Cotangent.exact_map_δ

/- Lemma 15.34.2 (3), tag `07E2`:
`H1Cotangent L M ⟶ M ⊗[L] Ω[L⁄K] ⟶ Ω[M⁄K]` is exact. -/
@[stacks 07E2 "Lemma 15.34.2 (3)"]
#check @H1Cotangent.exact_δ_mapBaseChange

/- Lemma 15.34.2 (4), tag `07E2`:
`M ⊗[L] Ω[L⁄K] ⟶ Ω[M⁄K] ⟶ Ω[M⁄L]` is exact. -/
@[stacks 07E2 "Lemma 15.34.2 (4)"]
#check @KaehlerDifferential.exact_mapBaseChange_map

/- Lemma 15.34.2 (5), tag `07E2`: the final map
`Ω[M⁄K] ⟶ Ω[M⁄L]` is surjective. -/
@[stacks 07E2 "Lemma 15.34.2 (5)"]
#check @KaehlerDifferential.map_surjective

end Algebra
