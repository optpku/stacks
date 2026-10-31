/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Tactic.CrossRefAttribute

/-!
# Subsets of scheme fibre products

This leaf owns the set-theoretic fibre product of two subsets along a pair of
scheme morphisms.  It is deliberately stated for arbitrary scheme morphisms,
rather than for a particular base field or an `Over`-category presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {W X Y Z S T : Scheme.{u}}

/-- The subset of `pullback f g` consisting of points whose first and second
projections belong to `A` and `B`, respectively. -/
@[stacks 047B "set-theoretic pullback subset", stacks 04Q0 "product pullback subset"]
def subset (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    Set (pullback f g : Scheme) :=
  {z | pullback.fst f g z ∈ A ∧ pullback.snd f g z ∈ B}

/-- A point of a scheme fibre product belongs to `subset f g A B` exactly
when its two projections belong to `A` and `B`. -/
@[simp]
theorem mem_subset_iff
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y)
    (z : (pullback f g : Scheme)) :
    z ∈ subset f g A B ↔ pullback.fst f g z ∈ A ∧ pullback.snd f g z ∈ B := Iff.rfl

/-- The set-theoretic fibre product is the intersection of the inverse images
under the two canonical projections. -/
theorem subset_eq_preimage_inter
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    subset f g A B =
      (pullback.fst f g) ⁻¹' A ∩ (pullback.snd f g) ⁻¹' B := rfl

/-- The first projection maps `subset f g A B` into `A`. -/
theorem fst_mapsTo_subset
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    Set.MapsTo (pullback.fst f g) (subset f g A B) A := by
  intro z hz
  exact hz.1

/-- The second projection maps `subset f g A B` into `B`. -/
theorem snd_mapsTo_subset
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    Set.MapsTo (pullback.snd f g) (subset f g A B) B := by
  intro z hz
  exact hz.2

/-- Enlarging either factor enlarges the corresponding subset of the scheme
fibre product. -/
theorem subset_mono
    {f : X ⟶ S} {g : Y ⟶ S} {A A' : Set X} {B B' : Set Y}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    subset f g A B ⊆ subset f g A' B' := by
  intro z hz
  exact ⟨hA hz.1, hB hz.2⟩

/-- A map between two pullback squares sends the subset determined by `A` and
`B` into the subset determined by their images under the two side maps. -/
@[stacks 04Q0 "pullback subset image bridge"]
theorem map_mapsTo_subset
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (h₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂)
    (A : Set W) (B : Set X) :
    Set.MapsTo (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁ h₂)
      (subset f₁ f₂ A B)
      (subset g₁ g₂ (i₁ '' A) (i₂ '' B)) := by
  intro z hz
  constructor
  · refine ⟨pullback.fst f₁ f₂ z, hz.1, ?_⟩
    symm
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  · refine ⟨pullback.snd f₁ f₂ z, hz.2, ?_⟩
    symm
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]

/-- A map between two pullback squares sends the subset determined by `A` and
`B` into the subset determined by target sets containing their respective images. -/
@[stacks 04Q0 "pullback subset target bridge"]
theorem map_mapsTo_subset_of_mapsTo
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (h₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂)
    (A : Set W) (B : Set X) (C : Set Y) (D : Set Z)
    (hi₁ : Set.MapsTo i₁ A C) (hi₂ : Set.MapsTo i₂ B D) :
    Set.MapsTo (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁ h₂)
      (subset f₁ f₂ A B) (subset g₁ g₂ C D) := by
  exact (map_mapsTo_subset f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁ h₂ A B).mono_right
    (subset_mono hi₁.image_subset hi₂.image_subset)

private theorem subset_closure_right_subset
    [AlgebraicGeometry.IsIntegral S] [Subsingleton S]
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    subset f g A (closure B) ⊆ closure (subset f g A B) := by
  intro z hz
  let x := pullback.fst f g z
  let a := X.fromSpecResidueField x
  let m := pullback.map (a ≫ f) g f g a (𝟙 Y) (𝟙 S) (by simp) (by simp)
  have hfst (t : (pullback (a ≫ f) g : Scheme)) : pullback.fst f g (m t) = x := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hsnd (t : (pullback (a ≫ f) g : Scheme)) :
      pullback.snd f g (m t) = pullback.snd (a ≫ f) g t := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id]
  -- Work in the fibre over the first projection of z.
  have hzrange : z ∈ Set.range m := by
    dsimp only [m]
    rw [range_map]
    simp [a, Scheme.range_fromSpecResidueField, x]
  obtain ⟨w, hw⟩ := hzrange
  have hm : Set.MapsTo m ((pullback.snd (a ≫ f) g) ⁻¹' B) (subset f g A B) := by
    intro t ht
    constructor
    · rw [hfst]
      exact hz.1
    · rw [hsnd]
      exact ht
  have hwB : pullback.snd (a ≫ f) g w ∈ closure B := by
    rw [← hsnd w, hw]
    exact hz.2
  -- The fibre projects openly to Y since its other factor maps to the one-point integral base.
  have hwclosure : w ∈ closure ((pullback.snd (a ≫ f) g) ⁻¹' B) :=
    (pullback.snd (a ≫ f) g).isOpenMap.preimage_closure_subset_closure_preimage hwB
  have h := hm.closure m.continuous hwclosure
  rwa [hw] at h

/-- Over a one-point integral base, the subset of a scheme fibre product
determined by the closures of two subsets is the closure of their fibre-product subset. -/
theorem subset_closure_eq_closure_subset
    [AlgebraicGeometry.IsIntegral S] [Subsingleton S]
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    subset f g (closure A) (closure B) = closure (subset f g A B) := by
  have hleft : subset f g (closure A) B ⊆ closure (subset f g A B) := by
    let e := pullbackSymmetry f g
    have he : Set.MapsTo e.inv (subset g f B A) (subset f g A B) := by
      intro z hz
      constructor
      · simpa [e, ← Scheme.Hom.comp_apply] using hz.2
      · simpa [e, ← Scheme.Hom.comp_apply] using hz.1
    intro z hz
    have hz' : e.hom z ∈ subset g f B (closure A) := by
      constructor
      · simpa [e, ← Scheme.Hom.comp_apply] using hz.2
      · simpa [e, ← Scheme.Hom.comp_apply] using hz.1
    have h := he.closure e.inv.continuous (subset_closure_right_subset g f B A hz')
    simpa [← Scheme.Hom.comp_apply] using h
  apply Set.Subset.antisymm
  · calc
      subset f g (closure A) (closure B) ⊆ closure (subset f g (closure A) B) :=
        subset_closure_right_subset f g (closure A) B
      _ ⊆ closure (closure (subset f g A B)) := closure_mono hleft
      _ = closure (subset f g A B) := closure_closure
  · intro z hz
    exact ⟨(fst_mapsTo_subset f g A B).closure (pullback.fst f g).continuous hz,
      (snd_mapsTo_subset f g A B).closure (pullback.snd f g).continuous hz⟩

/-- For two morphisms of schemes over a field, the pullback subset determined by
the closures of their ranges is the closure of the range of their tensor product. -/
theorem subset_closure_range_eq_closure_range_tensor
    {k : Type u} [Field k]
    {A X B Y : Over (Spec (CommRingCat.of k))} (f : A ⟶ X) (g : B ⟶ Y) :
    subset X.hom Y.hom
        (closure (Set.range f.left.base))
        (closure (Set.range g.left.base)) =
      (closure (Set.range ((f ⊗ₘ g).left.base)) : Set (pullback X.hom Y.hom : Scheme)) := by
  rw [subset_closure_eq_closure_subset]
  exact congrArg closure
    (range_map A.hom B.hom X.hom Y.hom f.left g.left (𝟙 _) (by simp) (by simp)).symm

end AlgebraicGeometry.Scheme.Pullback
