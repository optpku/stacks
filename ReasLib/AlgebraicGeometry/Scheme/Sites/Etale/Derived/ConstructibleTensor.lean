/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.DerivedCategory
  CategoryTheory.MonoidalCategory CategoryTheory.Sheaf
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u v

namespace AlgebraicGeometry.Scheme

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive` zeros.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in
/-- Over a Noetherian coefficient ring, the derived tensor product of two bounded-above
complexes of étale module sheaves with constructible cohomology is bounded above and has
constructible cohomology. -/
theorem etaleConstructible_derivedTensor
    {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [((X.smallEtaleTopology.W :
      MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
    [DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (n m : ℤ) (hK_le : K.IsLE n) (hL_le : L.IsLE m)
    (hK : ∀ k : ℤ,
      IsConstructibleEtaleModule
        (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
          (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
          IsFiniteTypeLocallyConstantModule F)
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K))
    (hL : ∀ k : ℤ,
      IsConstructibleEtaleModule
        (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
          (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
          IsFiniteTypeLocallyConstantModule F)
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj L)) :
    (∀ k : ℤ,
      IsConstructibleEtaleModule
        (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
          (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
          IsFiniteTypeLocallyConstantModule F)
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj (K ⊗ᴸ L))) ∧
      ∃ N : ℤ, (K ⊗ᴸ L).IsLE N :=
  sorry

end AlgebraicGeometry.Scheme
