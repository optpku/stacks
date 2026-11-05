/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleCloseds.Soberification.Functoriality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sober Targets of the Irreducible-Closed Soberification

This module records the canonical factorization of continuous maps through the
soberification when the target is sober.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

private theorem soberification_mem_open_iff {s : Set (IrreducibleCloseds X)}
    (hs : IsOpen s) (T : IrreducibleCloseds X) :
    T ∈ s ↔ ∃ x ∈ (T : Set X), toIrreducibleClosedsFun x ∈ s := by
  have hbasic : ∃ U : Opens X, s = IrreducibleCloseds.basicOpen U := by
    change GenerateOpen (Set.range fun U : Opens X ↦ IrreducibleCloseds.basicOpen U) s at hs
    induction hs with
    | basic s hs =>
        obtain ⟨U, rfl⟩ := hs
        exact ⟨U, rfl⟩
    | univ =>
        refine ⟨⊤, ?_⟩
        ext Z
        change Z ∈ Set.univ ↔ ((Z : Set X) ∩ Set.univ).Nonempty
        simpa only [Set.inter_univ, Set.mem_univ, true_iff] using Z.isIrreducible.nonempty
    | inter s t _ _ ihs iht =>
        obtain ⟨U, rfl⟩ := ihs
        obtain ⟨V, rfl⟩ := iht
        refine ⟨U ⊓ V, ?_⟩
        ext Z
        constructor
        · rintro ⟨hU, hV⟩
          exact Z.isIrreducible.isPreirreducible U V U.isOpen V.isOpen hU hV
        · rintro ⟨x, hx, hxU, hxV⟩
          exact ⟨⟨x, hx, hxU⟩, ⟨x, hx, hxV⟩⟩
    | sUnion S _ ih =>
        refine ⟨sSup {U : Opens X | IrreducibleCloseds.basicOpen U ∈ S}, ?_⟩
        ext Z
        change (∃ s ∈ S, Z ∈ s) ↔
          ∃ x ∈ (Z : Set X), x ∈ sSup {U : Opens X | IrreducibleCloseds.basicOpen U ∈ S}
        simp only [Opens.mem_sSup, Set.mem_setOf_eq]
        constructor
        · rintro ⟨s, hs, hZ⟩
          obtain ⟨U, rfl⟩ := ih s hs
          obtain ⟨x, hxZ, hxU⟩ := hZ
          exact ⟨x, hxZ, U, hs, hxU⟩
        · rintro ⟨x, hxZ, U, hU, hxU⟩
          exact ⟨IrreducibleCloseds.basicOpen U, hU, x, hxZ, hxU⟩
  obtain ⟨U, rfl⟩ := hbasic
  change ((T : Set X) ∩ (U : Set X)).Nonempty ↔
    ∃ x ∈ (T : Set X), (closure ({x} : Set X) ∩ (U : Set X)).Nonempty
  simp only [closure_inter_open_nonempty_iff U.isOpen, singleton_inter_nonempty]
  rfl

section

variable {Y : Type v} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]

/-- The canonical order equivalence from irreducible closed subsets of a sober space to its
points is continuous for the soberification topology. -/
theorem continuous_irreducibleSetEquivPoints :
    Continuous (irreducibleSetEquivPoints (α := Y) : IrreducibleCloseds Y → Y) := by
  refine continuous_def.2 fun U hU ↦ ?_
  have hpre :
      (irreducibleSetEquivPoints (α := Y) : IrreducibleCloseds Y → Y) ⁻¹' U =
        IrreducibleCloseds.basicOpen ⟨U, hU⟩ := by
    ext T
    exact (T.isIrreducible.isGenericPoint_genericPoint T.isClosed).mem_open_set_iff hU
  rw [hpre]
  exact isOpen_generateFrom_of_mem ⟨⟨U, hU⟩, rfl⟩

/-- The inverse of the canonical equivalence from irreducible closed subsets of a sober space to
its points is continuous for the soberification topology. -/
theorem continuous_irreducibleSetEquivPoints_symm :
    Continuous ((irreducibleSetEquivPoints (α := Y)).toEquiv.symm :
      Y → IrreducibleCloseds Y) := by
  apply continuous_generateFrom_iff.2
  rintro s ⟨U, rfl⟩
  have hpre :
      (irreducibleSetEquivPoints (α := Y)).toEquiv.symm ⁻¹' IrreducibleCloseds.basicOpen U =
        (U : Set Y) := by
    ext y
    change (closure ({y} : Set Y) ∩ (U : Set Y)).Nonempty ↔ y ∈ (U : Set Y)
    rw [closure_inter_open_nonempty_iff U.isOpen]
    exact singleton_inter_nonempty
  rw [hpre]
  exact U.isOpen

/-- The canonical homeomorphism from the soberification of a sober space to the space itself. -/
noncomputable def irreducibleSetHomeomorphPoints : IrreducibleCloseds Y ≃ₜ Y :=
  Homeomorph.mk (irreducibleSetEquivPoints (α := Y)).toEquiv
    (continuous_irreducibleSetEquivPoints (Y := Y))
    (continuous_irreducibleSetEquivPoints_symm (Y := Y))

/-- The underlying function of the canonical factorization of a continuous map through the
soberification. -/
noncomputable def TopologicalSpace.IrreducibleCloseds.soberificationLiftFun (f : C(X, Y))
    (T : IrreducibleCloseds X) : Y :=
  irreducibleSetEquivPoints (IrreducibleCloseds.map f f.continuous T)

/-- The canonical factorization through the soberification is continuous. -/
theorem TopologicalSpace.IrreducibleCloseds.continuous_soberificationLiftFun (f : C(X, Y)) :
    Continuous (IrreducibleCloseds.soberificationLiftFun f) := by
  refine continuous_def.2 fun U hU ↦ ?_
  have hpre : IrreducibleCloseds.soberificationLiftFun f ⁻¹' U =
      IrreducibleCloseds.basicOpen ⟨f ⁻¹' U, hU.preimage f.continuous⟩ := by
    ext T
    change (IrreducibleCloseds.map f f.continuous T).isIrreducible.genericPoint ∈ U ↔
      ((T : Set X) ∩ f ⁻¹' U).Nonempty
    rw [((IrreducibleCloseds.map f f.continuous T).isIrreducible.isGenericPoint_genericPoint
      (IrreducibleCloseds.map f f.continuous T).isClosed).mem_open_set_iff hU]
    change (closure (f '' (T : Set X)) ∩ U).Nonempty ↔
      ((T : Set X) ∩ f ⁻¹' U).Nonempty
    rw [closure_inter_open_nonempty_iff hU]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, hfx⟩
      exact ⟨x, hx, hfx⟩
    · rintro ⟨x, hx, hfx⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, hfx⟩
  rw [hpre]
  exact isOpen_generateFrom_of_mem ⟨⟨f ⁻¹' U, hU.preimage f.continuous⟩, rfl⟩

/-- The canonical continuous factorization of a map from `X` to a sober space. -/
noncomputable def TopologicalSpace.IrreducibleCloseds.soberificationLift (f : C(X, Y)) :
    C(IrreducibleCloseds X, Y) :=
  ⟨IrreducibleCloseds.soberificationLiftFun f,
    IrreducibleCloseds.continuous_soberificationLiftFun f⟩

/-- Evaluation of the canonical factor map through soberification. -/
@[simp]
theorem TopologicalSpace.IrreducibleCloseds.soberificationLift_apply (f : C(X, Y))
    (T : IrreducibleCloseds X) :
    IrreducibleCloseds.soberificationLift f T =
      irreducibleSetEquivPoints (IrreducibleCloseds.map f f.continuous T) := rfl

/-- The canonical soberification factor extends the original continuous map. -/
@[simp]
theorem TopologicalSpace.IrreducibleCloseds.soberificationLift_comp (f : C(X, Y)) :
    (IrreducibleCloseds.soberificationLift f).comp toIrreducibleCloseds = f := by
  apply ContinuousMap.ext
  intro x
  change irreducibleSetEquivPoints
      (IrreducibleCloseds.map f f.continuous (toIrreducibleCloseds x)) = f x
  have hmap : IrreducibleCloseds.map f f.continuous (toIrreducibleCloseds x) =
      (irreducibleSetEquivPoints (α := Y)).toEquiv.symm (f x) := by
    apply TopologicalSpace.IrreducibleCloseds.ext
    change closure (f '' closure ({x} : Set X)) = closure ({f x} : Set Y)
    rw [closure_image_closure f.continuous, image_singleton]
  rw [hmap]
  exact Equiv.apply_symm_apply (irreducibleSetEquivPoints (α := Y)).toEquiv (f x)

/-- A continuous map out of the soberification is determined by its composite with the canonical
map from `X`. -/
theorem TopologicalSpace.IrreducibleCloseds.soberificationLift_unique (f : C(X, Y))
    (g : C(IrreducibleCloseds X, Y))
    (hg : g.comp toIrreducibleCloseds = f) :
    g = IrreducibleCloseds.soberificationLift f := by
  apply ContinuousMap.ext
  intro T
  apply Inseparable.eq
  rw [inseparable_iff_forall_isOpen]
  intro U hU
  let h := IrreducibleCloseds.soberificationLift f
  have hcomp : g.comp toIrreducibleCloseds = h.comp toIrreducibleCloseds :=
    hg.trans (IrreducibleCloseds.soberificationLift_comp f).symm
  change T ∈ g ⁻¹' U ↔ T ∈ h ⁻¹' U
  rw [soberification_mem_open_iff (hU.preimage g.continuous),
    soberification_mem_open_iff (hU.preimage h.continuous)]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  change g (toIrreducibleCloseds x) ∈ U ↔ h (toIrreducibleCloseds x) ∈ U
  rw [show g (toIrreducibleCloseds x) = h (toIrreducibleCloseds x) from
    DFunLike.congr_fun hcomp x]

/-- Lemma 5.8.16 (1): the soberification map is universal among continuous maps from `X` to
sober spaces, represented by Mathlib's `QuasiSober` and `T0Space` components. -/
@[stacks 0A2N "universal property for sober targets"]
theorem toIrreducibleCloseds_universal (f : C(X, Y)) :
    ∃! g : C(IrreducibleCloseds X, Y), g.comp toIrreducibleCloseds = f :=
  ⟨IrreducibleCloseds.soberificationLift f, IrreducibleCloseds.soberificationLift_comp f,
    fun g hg ↦ IrreducibleCloseds.soberificationLift_unique f g hg⟩

end
