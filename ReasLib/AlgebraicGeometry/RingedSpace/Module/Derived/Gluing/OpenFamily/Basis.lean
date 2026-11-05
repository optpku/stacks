/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# BBD gluing on an overlap-generating open cover

The source theorem applies to arbitrary covering families that generate their pairwise
intersections. The basis version is a specialization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

/-- The remaining existence case of BBD gluing, when no finite subfamily covers the space.
The proof requires the transfinite induction and increasing-union gluing of 0D6C. -/
theorem existsRealization_of_no_finite_subcover (G : Gluing.OpenFamily X 𝓑)
    (hcover : sSup 𝓑 = ⊤) (hoverlap : GeneratesOverlaps X 𝓑)
    (hneg : G.NegativeSelfExtVanishing)
    (hinfinite : ¬ ∃ s : Finset (Opens X.carrier),
      (∀ U ∈ s, U ∈ 𝓑) ∧ iSup (fun U : s => (U : Opens X.carrier)) = ⊤) :
    G.HasRealization := sorry

/-- Existence in the BBD gluing lemma for an arbitrary overlap-generating open cover. -/
@[stacks 0D6C "existence in the BBD gluing lemma"]
theorem existsRealization (G : Gluing.OpenFamily X 𝓑)
    (hcover : sSup 𝓑 = ⊤) (hoverlap : GeneratesOverlaps X 𝓑)
    (hneg : G.NegativeSelfExtVanishing) : G.HasRealization := by
  classical
  by_cases hfinite : ∃ s : Finset (Opens X.carrier),
      (∀ U ∈ s, U ∈ 𝓑) ∧ iSup (fun U : s => (U : Opens X.carrier)) = ⊤
  · obtain ⟨s, hmem, hs⟩ := hfinite
    exact FiniteCover.existsRealization G (fun U : s => (U : Opens X.carrier))
      (fun U => hmem U U.property) hs hoverlap hneg
  · exact existsRealization_of_no_finite_subcover G hcover hoverlap hneg hfinite

/-- Theorem 20.45.8 (BBD gluing lemma), at the source cover and overlap hypotheses. -/
@[stacks 0D6C "BBD gluing lemma for derived modules"]
theorem existsUnique (G : Gluing.OpenFamily X 𝓑)
    (hcover : sSup 𝓑 = ⊤) (hoverlap : GeneratesOverlaps X 𝓑)
    (hneg : G.NegativeSelfExtVanishing) :
    G.HasRealization ∧
      ∀ {K L : ModuleDerived X} (R : G.Realization K) (S : G.Realization L),
        ∃! e : K ≅ L, IsCompatibleIso R S e := by
  exact ⟨existsRealization G hcover hoverlap hneg,
    fun R S => existsUniqueIso G hcover hoverlap hneg R S⟩

namespace Basis

private theorem sourceHypotheses (h𝓑 : Opens.IsBasis 𝓑) :
    sSup 𝓑 = ⊤ ∧ GeneratesOverlaps X 𝓑 := by
  have hgen (U : Opens X.carrier) :
      U ≤ sSup {V : Opens X.carrier | V ∈ 𝓑 ∧ V ≤ U} := by
    obtain ⟨S, hS, hU⟩ := Opens.isBasis_iff_cover.mp h𝓑 U
    rw [hU]
    exact sSup_le fun V hV => le_sSup ⟨hS hV, le_sSup hV⟩
  constructor
  · exact top_unique ((hgen ⊤).trans (sSup_le_sSup fun _ h => h.1))
  · intro U V _ _
    exact le_antisymm (hgen (U ⊓ V)) (sSup_le fun _ h => h.2)

/-- BBD gluing for coherent local derived modules on a basis, with negative
self-Ext vanishing, admit a realization unique up to a unique compatible isomorphism. -/
@[stacks 0D6C "BBD gluing lemma for derived modules"]
theorem existsUnique (G : Gluing.OpenFamily X 𝓑) (h𝓑 : Opens.IsBasis 𝓑)
    (hneg : G.NegativeSelfExtVanishing) :
    G.HasRealization ∧
      ∀ {K L : ModuleDerived X} (R : G.Realization K) (S : G.Realization L),
        ∃! e : K ≅ L, OpenFamily.IsCompatibleIso R S e := by
  exact OpenFamily.existsUnique G (sourceHypotheses h𝓑).1 (sourceHypotheses h𝓑).2 hneg

/-- Existence component of the BBD gluing lemma. -/
@[stacks 0D6C "existence in the BBD gluing lemma"]
theorem existsRealization (G : Gluing.OpenFamily X 𝓑) (h𝓑 : Opens.IsBasis 𝓑)
    (hneg : G.NegativeSelfExtVanishing) : G.HasRealization := by
  exact OpenFamily.existsRealization G (sourceHypotheses h𝓑).1 (sourceHypotheses h𝓑).2 hneg

/-- Uniqueness component of the BBD gluing lemma for two bundled realizations. -/
@[stacks 0D6C "uniqueness in the BBD gluing lemma"]
theorem existsUniqueIso (G : Gluing.OpenFamily X 𝓑) (h𝓑 : Opens.IsBasis 𝓑)
    (hneg : G.NegativeSelfExtVanishing)
    {K L : ModuleDerived X} (R : G.Realization K) (S : G.Realization L) :
    ∃! e : K ≅ L, OpenFamily.IsCompatibleIso R S e := by
  exact OpenFamily.existsUniqueIso G (sourceHypotheses h𝓑).1 (sourceHypotheses h𝓑).2 hneg R S

end Basis

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily

end
