/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Limit.Basic
public import Mathlib.Topology.Constructible

/-!
# Constructible subsets of inverse limits of spectral spaces

This module gives stagewise descriptions of constructible subsets of limits of cofiltered spectral
diagrams.
-/

@[expose] public section

universe v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} {C : Cone F}
variable [∀ j : J, SpectralSpace (F.obj j)]

/-- A constructible subset of a limiting cone over a cofiltered spectral diagram is pulled back
from a constructible subset at one stage. -/
@[stacks 0A2Y "constructible subsets descend"]
theorem constructible_eq_preimage_of_isLimit
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) :
    ∃ (i : J) (Ei : Set (F.obj i)), IsConstructible Ei ∧ C.π.app i ⁻¹' Ei = E := sorry

/-- An open constructible subset of a limiting cone is pulled back from a compact open subset at
one stage. -/
@[stacks 0A2Y "open constructible subsets descend"]
theorem open_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_open : IsOpen E) :
    ∃ (i : J) (Ei : CompactOpens (F.obj i)), C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := sorry

/-- A closed constructible subset of a limiting cone is pulled back from a closed constructible
subset at one stage. -/
@[stacks 0A2Y "closed constructible subsets descend"]
theorem closed_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_closed : IsClosed E) :
    ∃ (i : J) (Ei : Closeds (F.obj i)),
      IsConstructible (Ei : Set (F.obj i)) ∧ C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := sorry

end
