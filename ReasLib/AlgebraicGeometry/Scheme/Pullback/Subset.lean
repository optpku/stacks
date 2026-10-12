/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    z ∈ subset f g A B ↔ pullback.fst f g z ∈ A ∧ pullback.snd f g z ∈ B := sorry

/-- The set-theoretic fibre product is the intersection of the inverse images
under the two canonical projections. -/
theorem subset_eq_preimage_inter
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    subset f g A B =
      (pullback.fst f g) ⁻¹' A ∩ (pullback.snd f g) ⁻¹' B := sorry

/-- The first projection maps `subset f g A B` into `A`. -/
theorem fst_mapsTo_subset
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    Set.MapsTo (pullback.fst f g) (subset f g A B) A := sorry

/-- The second projection maps `subset f g A B` into `B`. -/
theorem snd_mapsTo_subset
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    Set.MapsTo (pullback.snd f g) (subset f g A B) B := sorry

/-- Enlarging either factor enlarges the corresponding subset of the scheme
fibre product. -/
theorem subset_mono
    {f : X ⟶ S} {g : Y ⟶ S} {A A' : Set X} {B B' : Set Y}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    subset f g A B ⊆ subset f g A' B' := sorry

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
      (subset g₁ g₂ (i₁ '' A) (i₂ '' B)) := sorry

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
      (subset f₁ f₂ A B) (subset g₁ g₂ C D) := sorry

/-- Over a one-point integral base, the subset of a scheme fibre product
determined by the closures of two subsets is the closure of their fibre-product subset. -/
theorem subset_closure_eq_closure_subset
    [AlgebraicGeometry.IsIntegral S] [Subsingleton S]
    (f : X ⟶ S) (g : Y ⟶ S) (A : Set X) (B : Set Y) :
    subset f g (closure A) (closure B) = closure (subset f g A B) := sorry

/-- For two morphisms of schemes over a field, the pullback subset determined by
the closures of their ranges is the closure of the range of their tensor product. -/
theorem subset_closure_range_eq_closure_range_tensor
    {k : Type u} [Field k]
    {A X B Y : Over (Spec (CommRingCat.of k))} (f : A ⟶ X) (g : B ⟶ Y) :
    subset X.hom Y.hom
        (closure (Set.range f.left.base))
        (closure (Set.range g.left.base)) =
      (closure (Set.range ((f ⊗ₘ g).left.base)) : Set (pullback X.hom Y.hom : Scheme)) := sorry

end AlgebraicGeometry.Scheme.Pullback
