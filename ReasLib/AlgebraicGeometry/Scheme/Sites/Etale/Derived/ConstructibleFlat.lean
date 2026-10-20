/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.DerivedCategory
  CategoryTheory.MonoidalCategory CategoryTheory.Sheaf

universe u v r

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory.{r} (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]
variable [((X.smallEtaleTopology.W :
    MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]

-- Local instance justification (defeq pin): derived-category quotients and cochain complexes require the canonical abelian preadditive zero morphisms.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable (F : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ)

/-- A cochain complex of étale `Λ`-module sheaves is constructible-flat when it is bounded,
termwise constructible, and termwise flat. -/
def constructibleFlatComplex : Prop :=
  (∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b) ∧
    (∀ degree : ℤ, constructibleModule X Λ (F.X degree)) ∧
      HomologicalComplex.IsTermwiseFlat F

/-- The constructible-flat complex predicate unfolds to boundedness, termwise constructibility,
and termwise flatness. -/
theorem constructibleFlatComplex_iff :
    constructibleFlatComplex X Λ F ↔
      (∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b) ∧
        (∀ degree : ℤ, constructibleModule X Λ (F.X degree)) ∧
          HomologicalComplex.IsTermwiseFlat F := sorry

/-- Constructible cohomology together with a flat representative in `[a, b]` yields a
constructible-flat representative supported in that same interval. -/
theorem exists_constructibleFlatComplex_of_hasFlatRepresentativeIn
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (a b : ℤ)
    (h_coh : ∀ degree : ℤ, constructibleModule X Λ
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) degree).obj K))
    (hK : DerivedCategory.HasFlatRepresentativeIn K a b) :
    ∃ F : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
      Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
        constructibleFlatComplex X Λ F := sorry

/-- A constructible Tor-finite étale derived object is exactly one represented by a bounded
constructible-flat cochain complex. -/
theorem constructibleTorFinite_iff_exists_constructibleFlatComplex
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    constructibleTorFinite X Λ K ↔
      ∃ F : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ constructibleFlatComplex X Λ F := sorry

end AlgebraicGeometry.Scheme.Etale.Derived
