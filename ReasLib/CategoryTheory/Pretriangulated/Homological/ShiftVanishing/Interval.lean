/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Extension.Interval
public import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing

@[expose] public section

/-!
# Finite Intervals for Shift Vanishing

This leaf records the order, translation, and closure API for the exact
shift-vanishing property of a functor.  It is independent of additive
extension stages.
-/

open CategoryTheory Limits ObjectProperty Pretriangulated
open scoped ZeroObject

universe vD vA uD uA

namespace CategoryTheory.Functor.shiftVanishingIn

section Basic

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- Every finite shift interval gives bounded shift vanishing. -/
@[stacks 05RE "finite interval implies bounded vanishing"]
theorem le_bounded (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) :
    H.shiftVanishingIn a b ≤ H.shiftVanishingBounded := by
  intro X hX
  constructor
  · show H.shiftVanishingPlus X
    refine ⟨a - 1, ?_⟩
    intro n hn
    have hn' : n ∉ Set.Icc a b := by
      intro h
      have := h.1
      omega
    exact (hX n hn').of_iso ((H.isoShift n).app X)
  · show H.shiftVanishingMinus X
    refine ⟨b + 1, ?_⟩
    intro n hn
    have hn' : n ∉ Set.Icc a b := by
      intro h
      have := h.2
      omega
    exact (hX n hn').of_iso ((H.isoShift n).app X)

/-- Enlarging the allowed interval preserves exact shift vanishing. -/
theorem mono (H : D ⥤ A) [H.ShiftSequence ℤ]
    {l u l' u' : ℤ} (hl : l' ≤ l) (hu : u ≤ u') :
    H.shiftVanishingIn l u ≤ H.shiftVanishingIn l' u' := by
  intro X hX n hn
  apply hX n
  intro h
  exact hn ⟨hl.trans h.1, h.2.trans hu⟩

/-- Vanishing of a shifted object translates to the corresponding interval on the object. -/
theorem of_shift (H : D ⥤ A) [H.ShiftSequence ℤ]
    {X : D} {a b k : ℤ} (hX : H.shiftVanishingIn a b (X⟦k⟧)) :
    H.shiftVanishingIn (a + k) (b + k) X := by
  intro n hn
  have hn' : n - k ∉ Set.Icc a b := by
    intro h
    apply hn
    constructor
    · change a + k ≤ n
      have := h.1
      omega
    · change n ≤ b + k
      have := h.2
      omega
  exact (hX (n - k) hn').of_iso ((H.shiftIso k (n - k) n (by omega)).app X).symm

/-- Exact shift vanishing is stable under retracts. -/
instance isStableUnderRetracts (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) :
    (H.shiftVanishingIn a b).IsStableUnderRetracts where
  of_retract r hY n hn := by
    let r' := r.map (H.shift n)
    exact IsZero.of_mono r'.i (hY n hn)

/-- Shifting generators through `[c, d]` translates their common vanishing interval by
the same endpoints. -/
@[stacks 0FX8]
theorem shiftInterval_le (H : D ⥤ A) [H.ShiftSequence ℤ]
    (E : ObjectProperty D) (a b c d : ℤ)
    (hE : E ≤ H.shiftVanishingIn a b) :
    E[c, d] ≤ H.shiftVanishingIn (a + c) (b + d) := by
  intro X hX
  obtain ⟨⟨k, hk⟩, Y, hY, ⟨e⟩⟩ := (ObjectProperty.prop_iSup_iff _ X).1 hX
  apply (H.shiftVanishingIn (a + c) (b + d)).prop_of_iso e.symm
  exact mono H (l := a + k) (u := b + k) (by have := hk.1; omega)
    (by have := hk.2; omega) Y (of_shift H (hE _ hY))

end Basic

section Triangulated

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- Exact shift vanishing contains every zero object. -/
instance containsZero (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    (a b : ℤ) :
    (H.shiftVanishingIn a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero D, fun n _ ↦ (H.shift n).map_isZero (isZero_zero D)⟩

/-- Exact shift vanishing is closed under middle terms of distinguished triangles. -/
instance isTriangulatedClosed₂ (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    (a b : ℤ) :
    (H.shiftVanishingIn a b).IsTriangulatedClosed₂ :=
  .mk' (by
    intro T hT h₁ h₃ n hn
    exact (H.homologySequence_exact₂ T hT n).isZero_of_both_isZero (h₁ n hn) (h₃ n hn))

/-- Exact shift vanishing is closed under binary coproducts. -/
instance isClosedUnderBinaryCoproducts
    (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ] (a b : ℤ) :
    (H.shiftVanishingIn a b).IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    refine (H.shiftVanishingIn a b).prop_of_iso ?_
      ((H.shiftVanishingIn a b).ext_of_isTriangulatedClosed₂ _
        (binaryBiproductTriangle_distinguished _ _)
        (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsColimit.coconePointsIsoOfNatIso (BinaryBiproduct.isColimit _ _) p.isColimit
      (diagramIsoPair p.diag).symm

/-- Exact shift vanishing is closed under finite coproducts. -/
instance isClosedUnderFiniteCoproducts
    (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ] (a b : ℤ) :
    (H.shiftVanishingIn a b).IsClosedUnderFiniteCoproducts := .mk'

end Triangulated

end CategoryTheory.Functor.shiftVanishingIn

namespace CategoryTheory.Functor.shiftVanishingBounded

section

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- Bounded shift vanishing is equivalent to vanishing outside some finite interval. -/
@[stacks 05RE "bounded vanishing interval characterization"]
theorem mem_iff_exists_interval (H : D ⥤ A) [H.ShiftSequence ℤ] (X : D) :
    H.shiftVanishingBounded X ↔ ∃ a b : ℤ, H.shiftVanishingIn a b X := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, ?_⟩
    intro n hn
    by_cases hna : n ≤ a
    · show IsZero ((H.shift n).obj X)
      exact (ha n hna).of_iso ((H.isoShift n).app X).symm
    · show IsZero ((H.shift n).obj X)
      have hbn : b ≤ n := by
        by_contra h
        exact hn ⟨by omega, by omega⟩
      exact (hb n hbn).of_iso ((H.isoShift n).app X).symm
  · rintro ⟨a, b, hX⟩
    exact shiftVanishingIn.le_bounded H a b X hX

end

end CategoryTheory.Functor.shiftVanishingBounded
