/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Stability

/-!
# Refinements of fpqc covers

Fpqc covers of affine schemes have selected finite refinements by affine open
subschemes of their members.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.FpqcCover

/-- An fpqc cover of an affine scheme has a selected finite standard fpqc
refinement whose component maps into the original cover are open immersions. -/
theorem exists_standardRefinement {T : Scheme.{u}} [IsAffine T]
    (𝒰 : FpqcCover.{u, v} T) :
    ∃ 𝒱 : StandardFpqcCover T,
      ∃ φ : SemiRepresentableFamily.Over.Hom 𝒱.toOverFamily (ofArrows 𝒰.X 𝒰.f),
        ∀ j : Fin 𝒱.n, IsOpenImmersion ((φ.f j).left) := sorry

/-- A selected finite standard refinement gives the refinement relation,
open-immersion component maps, and their commuting equations over the target. -/
theorem exists_standardRefinement_spec {T : Scheme.{u}} [IsAffine T]
    (𝒰 : FpqcCover.{u, v} T) :
    ∃ 𝒱 : StandardFpqcCover T,
      Refines 𝒱.toOverFamily (ofArrows 𝒰.X 𝒰.f) ∧
        ∀ j : Fin 𝒱.n, ∃ i : 𝒰.I₀, ∃ g : 𝒱.U j ⟶ 𝒰.X i,
          IsOpenImmersion g ∧ g ≫ 𝒰.f i = 𝒱.map j := by
  rcases exists_standardRefinement 𝒰 with ⟨𝒱, φ, hφ⟩
  refine ⟨𝒱, ⟨φ⟩, ?_⟩
  intro j
  refine ⟨φ.α j, (φ.f j).left, hφ j, ?_⟩
  change (φ.f j).left ≫ 𝒰.f (φ.α j) = 𝒱.map j
  simpa using Over.w (φ.f j)

end AlgebraicGeometry.FpqcCover

namespace AlgebraicGeometry.Scheme

/-- A pointwise flat family is fpqc-covering if every affine base change admits
a standard fpqc cover refining the pulled-back family. -/
theorem fpqcCovering_of_flat_of_affine_pullback_standard_refinement
    {T : Scheme.{u}} {ι : Type v}
    (X : ι → Over T) (hflat : ∀ i : ι, Flat (X i).hom)
    (hrefines :
      ∀ ⦃Z : Scheme.{u}⦄ (hZ : IsAffine Z) (h : Z ⟶ T),
        ∃ 𝒰 : StandardFpqcCover Z,
          Refines 𝒰.toOverFamily
            (ofArrows (fun i ↦ pullback h (X i).hom)
              (fun i ↦ pullback.fst h (X i).hom))) :
    Scheme.FpqcCovering X := sorry

end AlgebraicGeometry.Scheme
