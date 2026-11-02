/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Locality of at-worst-nodal morphisms of algebraic spaces

At-worst-nodality of relative dimension 1 admits base-change, étale-cover,
étale-square, and Zariski-cover characterizations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace AtWorstNodal

/-- Every base change along a morphism from a scheme is at worst nodal of
relative dimension 1. -/
abbrev baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallScheme (@AtWorstNodal S) f

/-- The scheme-base-change condition is equivalent to at-worst-nodality of
every canonical projection after base change from a scheme. -/
theorem baseChangeOnSchemes_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    baseChangeOnSchemes f ↔
      ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
        AtWorstNodal (pullbackAlongScheme.snd f g) :=
  Iff.rfl

/-- Every base change along a morphism from an affine scheme is at worst nodal
of relative dimension 1. -/
abbrev baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.forallAffine (@AtWorstNodal S) f

/-- The affine-scheme-base-change condition is equivalent to at-worst-nodality
of every canonical projection after base change from an affine scheme. -/
theorem baseChangeOnAffineSchemes_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    baseChangeOnAffineSchemes f ↔
      ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
        IsAffine Z.left → AtWorstNodal (pullbackAlongScheme.snd f g) :=
  Iff.rfl

/-- There is a surjective étale morphism from a scheme to the target along
which the base change is at worst nodal of relative dimension 1. -/
abbrev existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleTarget (@AtWorstNodal S) f

/-- The target-atlas condition is equivalent to the existence of a surjective
étale scheme cover with at-worst-nodal base-change projection. -/
theorem existsSurjectiveEtaleTarget_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleTarget f ↔
      ∃ (V : Over S) (b : ofOver V ⟶ Y),
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          Surjective b ∧ AtWorstNodal (pullbackAlongScheme.snd f b) :=
  Iff.rfl

/-- There is a surjective étale morphism from a scheme to the source whose
composite with the given morphism is at worst nodal of relative dimension 1. -/
abbrev existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleSource (@AtWorstNodal S) f

/-- The source-atlas condition is equivalent to the existence of a surjective
étale scheme cover whose composite is at worst nodal. -/
theorem existsSurjectiveEtaleSource_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsSurjectiveEtaleSource f ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
          Surjective φ ∧ AtWorstNodal (φ ≫ f) :=
  Iff.rfl

/-- There is a commutative scheme square with étale vertical arrows,
surjective source vertical arrow, and at-worst-nodal top arrow of relative
dimension 1. -/
abbrev existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsEtaleSquare (@AlgebraicGeometry.AtWorstNodal) f

/-- The existential étale-square condition is equivalent to a commutative
scheme square with étale vertical arrows, surjective source vertical arrow,
and at-worst-nodal top arrow. -/
theorem existsEtaleSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsEtaleSquare f ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Surjective a ∧ AlgebraicGeometry.AtWorstNodal h.left :=
  Iff.rfl

/-- There are Zariski coverings of the target and of each full inverse image
on which the canonical restricted morphisms are at worst nodal of relative
dimension 1. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ 𝒰 : ZariskiCover.{u, v} (overPullbackObj (𝒱.f i) (Over.mk f)),
      ∀ j, AtWorstNodal (𝒰.f j ≫ overPullbackSnd (𝒱.f i) (Over.mk f))

/-- The Zariski-cover condition is equivalent to covers of the target and its
canonical inverse images whose restricted projections are at worst nodal. -/
theorem existsZariskiCover_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsZariskiCover.{u, v} f ↔
      ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
        ∃ 𝒰 : ZariskiCover.{u, v} (overPullbackObj (𝒱.f i) (Over.mk f)),
          ∀ j, AtWorstNodal (𝒰.f j ≫ overPullbackSnd (𝒱.f i) (Over.mk f)) :=
  Iff.rfl

/-- The canonical inverse-image presentation agrees with the generic criterion
using open subspaces whose images are the full inverse images. These are
equivalent presentations, rather than definitionally equal predicates.
Stacks, Tag 0DSG (8), `tex/spaces-more-morphisms.tex:13356–13359`. -/
theorem existsZariskiCover_iff_criteria {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    existsZariskiCover.{u, v} f ↔
      Locality.Criteria.existsZariskiCover.{u, v} (@AtWorstNodal S) f :=
  sorry

end AtWorstNodal

/-- At-worst-nodality of relative dimension 1 for a morphism of algebraic spaces
is equivalent to scheme and affine-scheme base-change tests, surjective étale
target and source atlas tests, universal and existential étale scheme-square
tests, and Zariski tests on the target and its full inverse images. -/
theorem atWorstNodal_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ AtWorstNodal f
      , AtWorstNodal.baseChangeOnSchemes f
      , AtWorstNodal.baseChangeOnAffineSchemes f
      , AtWorstNodal.existsSurjectiveEtaleTarget f
      , AtWorstNodal.existsSurjectiveEtaleSource f
      , etaleLocal
          (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f
      , AtWorstNodal.existsEtaleSquare f
      , AtWorstNodal.existsZariskiCover.{u, v} f ] := by
  have hP : (@AtWorstNodal S : MorphismProperty (AlgebraicSpace S)) =
      etaleLocal (@AlgebraicGeometry.AtWorstNodal) := by
    funext U V g
    exact propext (atWorstNodal_iff_etaleLocal g)
  have hlocal := Locality.Criteria.etaleLocal_tfae.{u, v}
    (@AlgebraicGeometry.AtWorstNodal) f
  rw [propext (AtWorstNodal.existsZariskiCover_iff_criteria.{u, v} f)]
  simpa only [AtWorstNodal.baseChangeOnSchemes,
    AtWorstNodal.baseChangeOnAffineSchemes,
    AtWorstNodal.existsSurjectiveEtaleTarget,
    AtWorstNodal.existsSurjectiveEtaleSource, AtWorstNodal.existsEtaleSquare, hP]
    using hlocal

end AlgebraicGeometry.AlgebraicSpace
