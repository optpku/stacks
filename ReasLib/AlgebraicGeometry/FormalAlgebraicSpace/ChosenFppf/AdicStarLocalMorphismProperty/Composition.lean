/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty
public import ReasLib.RingTheory.Topology.AdicStar.Composition

/-!
# Composition of local morphism properties of locally adic-star spaces

Composition-stable local properties of continuous homomorphisms of adic-star
rings induce composition-stable properties of locally adic-star formal
algebraic spaces on a size-closed chosen big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [hSheafify : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [hPullbacks : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable {f : X ⟶ Y} {g : Y ⟶ Z}

include hSheafify hPullbacks

/-- Universal affine étale testing of a composition-stable local property of
continuous homomorphisms of adic-star rings is preserved by composition of
morphisms of locally adic-star formal algebraic spaces on a size-closed site. -/
theorem etaleAffineLocally.comp
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (h_stable : IsAdicStarRing.IsStableUnderComposition P)
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P (f ≫ g) := sorry

/-- Target-cover testing of a composition-stable local property of continuous
homomorphisms of adic-star rings is preserved by composition of morphisms of
locally adic-star formal algebraic spaces on a size-closed site. -/
theorem existsCoverOnTarget.comp
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (h_stable : IsAdicStarRing.IsStableUnderComposition P)
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P (f ≫ g) := sorry

/-- Source-cover testing of a composition-stable local property of continuous
homomorphisms of adic-star rings is preserved by composition of morphisms of
locally adic-star formal algebraic spaces on a size-closed site. -/
theorem existsCoverOnSource.comp
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (h_stable : IsAdicStarRing.IsStableUnderComposition P)
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P (f ≫ g) := sorry

end AlgebraicGeometry.IsLocallyAdicStar
