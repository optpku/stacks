/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sober.Soberification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Kolmogorov Reflection through Soberification

The range of the point-closure map realizes the Kolmogorov reflection and has
the expected universal property for continuous maps into `T0Space`s.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- The canonical continuous map from `X` to the range of its soberification map. -/
def toIrreducibleClosedsRange :
    C(X, Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X)) :=
  ⟨Set.rangeFactorization toIrreducibleCloseds,
    toIrreducibleCloseds.continuous.rangeFactorization⟩

/-- The canonical equivalence from the Kolmogorov reflection to the range of the soberification
map. -/
noncomputable def separationQuotientEquivRange :
    SeparationQuotient X ≃ Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X) :=
  (Quotient.congrRight (r := inseparableSetoid X)
      (r' := Setoid.ker (toIrreducibleCloseds : X → IrreducibleCloseds X))
      (fun x y ↦ (toIrreducibleCloseds_eq_iff_inseparable (x := x) (y := y)).symm)).trans
    (Setoid.quotientKerEquivRange (toIrreducibleCloseds : X → IrreducibleCloseds X))

/-- The canonical equivalence from the Kolmogorov reflection to the soberification range is
continuous. -/
theorem continuous_separationQuotientEquivRange :
    Continuous (separationQuotientEquivRange (X := X)) := by
  apply SeparationQuotient.isQuotientMap_mk.continuous_iff.2
  change Continuous (toIrreducibleClosedsRange (X := X))
  exact toIrreducibleClosedsRange.continuous

/-- The inverse of the canonical equivalence from the Kolmogorov reflection to the
soberification range is continuous. -/
theorem continuous_separationQuotientEquivRange_symm :
    Continuous (separationQuotientEquivRange (X := X)).symm := by
  refine continuous_def.2 ?_
  intro s hs
  let U : Opens X :=
    ⟨SeparationQuotient.mk ⁻¹' s, hs.preimage SeparationQuotient.continuous_mk⟩
  refine isOpen_induced_iff.2
    ⟨IrreducibleCloseds.basicOpen U, isOpen_generateFrom_of_mem ⟨U, rfl⟩, ?_⟩
  ext z
  obtain ⟨x, hx⟩ := z.property
  have hz : toIrreducibleClosedsRange x = z := Subtype.ext hx
  subst z
  change toIrreducibleCloseds x ∈ IrreducibleCloseds.basicOpen U ↔
    (separationQuotientEquivRange (X := X)).symm
      (separationQuotientEquivRange (X := X) (SeparationQuotient.mk x)) ∈ s
  rw [Equiv.symm_apply_apply]
  change (closure ({x} : Set X) ∩ (U : Set X)).Nonempty ↔ x ∈ (U : Set X)
  rw [closure_inter_open_nonempty_iff U.isOpen]
  exact singleton_inter_nonempty

/-- The range of the soberification map is canonically homeomorphic to the Kolmogorov
reflection `SeparationQuotient X`. -/
noncomputable def separationQuotientHomeomorphRange :
    SeparationQuotient X ≃ₜ Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X) :=
  Homeomorph.mk (separationQuotientEquivRange (X := X))
    (continuous_separationQuotientEquivRange (X := X))
    (continuous_separationQuotientEquivRange_symm (X := X))

/-- The homeomorphism from the Kolmogorov reflection to the soberification range sends the
class of a point to its point closure. -/
@[simp]
theorem separationQuotientHomeomorphRange_mk (x : X) :
    separationQuotientHomeomorphRange (X := X) (SeparationQuotient.mk x) =
      toIrreducibleClosedsRange x := rfl

section

variable {Y : Type v} [TopologicalSpace Y] [T0Space Y]

/-- A continuous map to a Kolmogorov space identifies inseparable points. -/
theorem ContinuousMap.eq_of_inseparable (f : C(X, Y)) (x y : X)
    (hxy : Inseparable x y) : f x = f y :=
  (hxy.map f.continuous).eq

/-- The canonical continuous factorization of a map through the Kolmogorov reflection. -/
def SeparationQuotient.liftContinuous (f : C(X, Y)) : C(SeparationQuotient X, Y) :=
  ⟨SeparationQuotient.lift f (ContinuousMap.eq_of_inseparable f),
    SeparationQuotient.continuous_lift f.continuous⟩

/-- The canonical factor through the Kolmogorov reflection extends the original map. -/
@[simp]
theorem SeparationQuotient.liftContinuous_comp_mk (f : C(X, Y)) :
    (SeparationQuotient.liftContinuous f).comp
      (SeparationQuotient.mkContinuous (X := X)) = f := by
  ext x
  rfl

/-- A continuous map out of the Kolmogorov reflection is determined by its composite with the
quotient map. -/
theorem SeparationQuotient.liftContinuous_unique (f : C(X, Y))
    (g : C(SeparationQuotient X, Y))
    (hg : g.comp (SeparationQuotient.mkContinuous (X := X)) = f) :
    g = SeparationQuotient.liftContinuous f := by
  ext q
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk q
  exact DFunLike.congr_fun hg x

/-- The canonical continuous factorization of a map through the range of the soberification
map. -/
noncomputable def toIrreducibleClosedsRangeLift (f : C(X, Y)) :
    C(Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X), Y) :=
  (SeparationQuotient.liftContinuous f).comp
    ⟨(separationQuotientHomeomorphRange (X := X)).symm,
      (separationQuotientHomeomorphRange (X := X)).symm.continuous⟩

/-- The canonical factor through the soberification range extends the original map. -/
@[simp]
theorem toIrreducibleClosedsRangeLift_comp (f : C(X, Y)) :
    (toIrreducibleClosedsRangeLift f).comp toIrreducibleClosedsRange = f := by
  ext x
  change SeparationQuotient.liftContinuous f
    ((separationQuotientHomeomorphRange (X := X)).symm
      (toIrreducibleClosedsRange x)) = f x
  rw [← separationQuotientHomeomorphRange_mk, Homeomorph.symm_apply_apply]
  rfl

/-- A continuous map out of the soberification range is determined by its composite with the
canonical range map. -/
theorem toIrreducibleClosedsRangeLift_unique (f : C(X, Y))
    (g : C(Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X), Y))
    (hg : g.comp toIrreducibleClosedsRange = f) :
    g = toIrreducibleClosedsRangeLift f := by
  ext z
  obtain ⟨x, hx⟩ := z.property
  have hz : toIrreducibleClosedsRange x = z := Subtype.ext hx
  rw [← hz]
  exact (DFunLike.congr_fun hg x).trans
    (DFunLike.congr_fun (toIrreducibleClosedsRangeLift_comp f) x).symm

/-- Lemma 5.8.16 (4): the range of the soberification map is universal for continuous maps from
`X` into Kolmogorov spaces. -/
@[stacks 0A2N "universal property of the Kolmogorov image"]
theorem toIrreducibleClosedsImage_universal (f : C(X, Y)) :
    ∃! g : C(Set.range (toIrreducibleCloseds : X → IrreducibleCloseds X), Y),
      g.comp toIrreducibleClosedsRange = f :=
  ⟨toIrreducibleClosedsRangeLift f, toIrreducibleClosedsRangeLift_comp f,
    fun g hg ↦ toIrreducibleClosedsRangeLift_unique f g hg⟩

end
