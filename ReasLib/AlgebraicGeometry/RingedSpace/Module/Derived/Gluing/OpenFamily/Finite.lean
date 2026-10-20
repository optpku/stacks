/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Overlap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Open-family gluing over finite covers
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily.FiniteCover

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

/-- Lemma 20.45.6: a finite cover by members of an overlap-generating family admits a global
realization, unique up to a unique compatible isomorphism. -/
@[stacks 0D6A "derived gluing over a finite open cover"]
theorem existsUnique (G : Gluing.OpenFamily X 𝓑)
    {ι : Type v} [Finite ι] (cover : ι → Opens X.carrier)
    (hmem : ∀ i, cover i ∈ 𝓑) (hcover : iSup cover = ⊤)
    (hoverlap : OpenFamily.GeneratesOverlaps X 𝓑)
    (hneg : G.NegativeSelfExtVanishing) :
    G.HasRealization ∧
      ∀ {K L : ModuleDerived X} (R : G.Realization K) (S : G.Realization L),
        ∃! e : K ≅ L, OpenFamily.IsCompatibleIso R S e := sorry

/-- Existence component of finite-cover open-family gluing. -/
@[stacks 0D6A "existence of a finite-cover derived realization"]
theorem existsRealization (G : Gluing.OpenFamily X 𝓑)
    {ι : Type v} [Finite ι] (cover : ι → Opens X.carrier)
    (hmem : ∀ i, cover i ∈ 𝓑) (hcover : iSup cover = ⊤)
    (hoverlap : OpenFamily.GeneratesOverlaps X 𝓑)
    (hneg : G.NegativeSelfExtVanishing) : G.HasRealization := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily.FiniteCover

end
