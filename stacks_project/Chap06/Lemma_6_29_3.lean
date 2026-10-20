/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.InverseLimit.PullbackSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

variable {I : Type u} [Category.{v} I]
variable (F : I ⥤ TopCat.{max u v})

/- Lemma 6.29.3: for a cofiltered diagram of spectral spaces with spectral transition maps, the
canonical comparison from the colimit of `f_a⁻¹ 𝒢(f_a⁻¹(U))` over arrows `a : j ⟶ i` to
`p_i⁻¹𝒢(p_i⁻¹(U))` is an isomorphism for every quasi-compact open `U ⊆ X_i`. -/
@[stacks 0A32]
recall TopCat.Sheaf.InverseLimit.pullbackSectionColimitComparison_isIso
