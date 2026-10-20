/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# BBD gluing on a basis of opens
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily.Basis

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

/-- Theorem 20.45.8 (BBD gluing lemma): coherent local derived modules on a basis, with negative
self-Ext vanishing, admit a realization unique up to a unique compatible isomorphism. -/
@[stacks 0D6C "BBD gluing lemma for derived modules"]
theorem existsUnique (G : Gluing.OpenFamily X 𝓑) (h𝓑 : Opens.IsBasis 𝓑)
    (hneg : G.NegativeSelfExtVanishing) :
    G.HasRealization ∧
      ∀ {K L : ModuleDerived X} (R : G.Realization K) (S : G.Realization L),
        ∃! e : K ≅ L, OpenFamily.IsCompatibleIso R S e := sorry

/-- Existence component of the BBD gluing lemma. -/
@[stacks 0D6C "existence in the BBD gluing lemma"]
theorem existsRealization (G : Gluing.OpenFamily X 𝓑) (h𝓑 : Opens.IsBasis 𝓑)
    (hneg : G.NegativeSelfExtVanishing) : G.HasRealization := sorry

/-- Uniqueness component of the BBD gluing lemma for two bundled realizations. -/
@[stacks 0D6C "uniqueness in the BBD gluing lemma"]
theorem existsUniqueIso (G : Gluing.OpenFamily X 𝓑) (h𝓑 : Opens.IsBasis 𝓑)
    (hneg : G.NegativeSelfExtVanishing)
    {K L : ModuleDerived X} (R : G.Realization K) (S : G.Realization L) :
    ∃! e : K ≅ L, OpenFamily.IsCompatibleIso R S e := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily.Basis

end
