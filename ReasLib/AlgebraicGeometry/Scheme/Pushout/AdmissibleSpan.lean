/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Pushout

/-- The admissibility conditions on a span of schemes over a fixed base used in
the scheme-pushout construction. -/
class IsAdmissibleSpan {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) : Prop
    extends IsClosedImmersion i.left, IsIntegralHom j.left where
  /-- Every fibre of `j` maps under `i` into an affine open of `X`. -/
  exists_affineOpen (y : Y.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∀ z : Z.left, j.left z = y → i.left z ∈ U

namespace IsAdmissibleSpan

variable {S : Scheme.{u}} {Z X Y : Over S} {i : Z ⟶ X} {j : Z ⟶ Y}

/-- The span consisting of two identity morphisms is admissible. -/
instance instIdentity (X : Over S) : IsAdmissibleSpan (𝟙 X) (𝟙 X) where
  toIsClosedImmersion := by
    change IsClosedImmersion (𝟙 X.left)
    infer_instance
  toIsIntegralHom := by
    change IsIntegralHom (𝟙 X.left)
    infer_instance
  exists_affineOpen y := by
    obtain ⟨U, hU, hyU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X.left) (U := ⊤) (x := y) (by trivial)
    refine ⟨U, hU, ?_⟩
    intro z hz
    change z = y at hz
    change z ∈ U
    exact hz.symm ▸ hyU

/-- The three conditions characterizing an admissible span. -/
theorem iff (i : Z ⟶ X) (j : Z ⟶ Y) :
    IsAdmissibleSpan i j ↔
      IsClosedImmersion i.left ∧ IsIntegralHom j.left ∧
        ∀ y : Y.left, ∃ U : X.left.Opens, IsAffineOpen U ∧
          ∀ z : Z.left, j.left z = y → i.left z ∈ U := by
  constructor
  · intro h
    exact ⟨h.toIsClosedImmersion, h.toIsIntegralHom, h.exists_affineOpen⟩
  · rintro ⟨hi, hj, h⟩
    exact { toIsClosedImmersion := hi, toIsIntegralHom := hj, exists_affineOpen := h }

/-- The fibre over a point is contained in the inverse image of a suitable affine open. -/
theorem fiber_subset_preimage [IsAdmissibleSpan i j] (y : Y.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      {z : Z.left | j.left z = y} ⊆ (i.left ⁻¹ᵁ U : Set Z.left) := by
  obtain ⟨U, hU, h⟩ := exists_affineOpen (i := i) (j := j) y
  exact ⟨U, hU, fun z hz ↦ h z hz⟩

/-- Every point in one target of an admissible span has an affine neighborhood whose
inverse image agrees with that of an affine open in the other target. -/
theorem exists_affineOpen_preimage_eq [IsAdmissibleSpan i j] (y : Y.left) :
    ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (V : Y.left.Opens) (_ : IsAffineOpen V),
      i.left ⁻¹ᵁ U = j.left ⁻¹ᵁ V ∧ y ∈ V := sorry

end IsAdmissibleSpan

end AlgebraicGeometry.Scheme.Pushout
