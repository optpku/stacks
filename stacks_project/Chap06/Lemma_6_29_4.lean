/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.InverseLimit.System
import StacksCheckRecall

@[expose] public section

/- Lemma 6.29.4: for a cofiltered diagram of spectral spaces with spectral transition maps and a
compatible inverse system of sheaves, the canonical map
`colim_{a : j ⟶ i} 𝓕ⱼ(fₐ⁻¹(Uᵢ)) ⟶ (colimⱼ pⱼ⁻¹ 𝓕ⱼ)(pᵢ⁻¹(Uᵢ))`
is an isomorphism for every quasi-compact open `Uᵢ ⊆ F.obj i`. -/
@[stacks 0A33]
recall TopCat.Sheaf.InverseLimit.SheafSystem.projectionOpenSectionsComparison_isIso
