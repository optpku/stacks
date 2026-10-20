module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic

/-!
# Smoothness under base change

This file compares pointwise smoothness and smooth loci across cartesian squares of schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- In a cartesian square, pointwise smoothness is preserved and reflected when the original
morphism is flat and locally of finite presentation. -/
theorem smoothAt_iff_of_isPullback_of_flat
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f] (x' : X') :
    f'.SmoothAt x' ↔ f.SmoothAt (g' x') := sorry

/-- In a cartesian square over a flat base morphism, pointwise smoothness is preserved and
reflected when the original morphism is locally of finite presentation. -/
theorem smoothAt_iff_of_isPullback_of_flat_base
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g] (x' : X') :
    f'.SmoothAt x' ↔ f.SmoothAt (g' x') := sorry

/-- In a cartesian square, the smooth locus is the inverse image of the original smooth locus
when the original morphism is flat and locally of finite presentation. -/
theorem smoothAt_open_eq_preimage_of_isPullback_of_flat
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
    (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | f.SmoothAt x})
    (hW' : (W' : Set X') = {x' : X' | f'.SmoothAt x'}) :
    W' = g' ⁻¹ᵁ W := by
  apply SetLike.coe_injective
  ext x'
  change x' ∈ (W' : Set X') ↔ g' x' ∈ (W : Set X)
  rw [hW, hW']
  exact smoothAt_iff_of_isPullback_of_flat g' f' f g hcart x'

/-- In a cartesian square over a flat base morphism, the smooth locus is the inverse image of
the original smooth locus when the original morphism is locally of finite presentation. -/
theorem smoothAt_open_eq_preimage_of_isPullback_of_flat_base
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g]
    (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | f.SmoothAt x})
    (hW' : (W' : Set X') = {x' : X' | f'.SmoothAt x'}) :
    W' = g' ⁻¹ᵁ W := by
  apply SetLike.coe_injective
  ext x'
  change x' ∈ (W' : Set X') ↔ g' x' ∈ (W : Set X)
  rw [hW, hW']
  exact smoothAt_iff_of_isPullback_of_flat_base g' f' f g hcart x'

end AlgebraicGeometry.Scheme.Hom
