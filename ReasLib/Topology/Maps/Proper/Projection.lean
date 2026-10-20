/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Maps.Proper.UniversallyClosed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed Product Projections

The forward compactness-to-closed-projection implication is in Mathlib.  This
leaf adds the converse criterion used to recognize compact spaces.
-/

@[expose] public section

universe u v

/-- Lemma 5.17.3: a space is compact exactly when every product projection
onto a space in a universe containing it is a closed map. -/
@[stacks 005P]
theorem compactSpace_iff_forall_isClosedMap_fst
    (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔ ∀ (Z : Type (max u v)) [TopologicalSpace Z],
      IsClosedMap (Prod.fst : Z × X → Z) := by
  constructor
  · intro hX Z _
    letI := hX
    exact isClosedMap_fst_of_compactSpace
  · intro h
    have hproj (Z : Type u) [TopologicalSpace Z] :
        IsClosedMap (Prod.fst : Z × X → Z) := by
      let eZ : ULift.{v} Z ≃ₜ Z := Homeomorph.ulift
      have hLift : IsClosedMap (Prod.fst : ULift.{v} Z × X → ULift.{v} Z) := h _
      have hcomp := eZ.isClosedMap.comp
        (hLift.comp (eZ.symm.prodCongr (Homeomorph.refl X)).isClosedMap)
      simpa [eZ, Function.comp_def, Homeomorph.coe_prodCongr] using hcomp
    rw [← isProperMap_const_iff (X := X) (Y := PUnit.{1}) PUnit.unit]
    rw [isProperMap_iff_universally_closed]
    refine ⟨continuous_const, fun Z _ ↦ ?_⟩
    rw [show (Prod.map (fun _ : X => PUnit.unit) id : X × Z → PUnit.{1} × Z) =
        (Homeomorph.punitProd.{u, 0} Z).symm ∘ Prod.fst ∘ Prod.swap by
      funext p
      rfl]
    exact (Homeomorph.punitProd.{u, 0} Z).symm.isClosedMap.comp
      ((hproj Z).comp (Homeomorph.prodComm X Z).isClosedMap)
