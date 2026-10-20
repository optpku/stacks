/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.FiniteSum
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.Sheaf

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive` zeros.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in
/-- A bounded-above derived module sheaf on a quasi-compact and quasi-separated scheme
over a Noetherian coefficient ring has constructible cohomology if and only if it admits
a complex representative with the same upper bound whose terms are finite sums of
regular constant module sheaves extended by zero from affine étale schemes. -/
theorem mem_etaleConstructible_iff_iso_jShriekSum
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (n : ℤ) [K.IsLE n] :
    (∀ k : ℤ,
        IsConstructibleEtaleModule
          (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
            (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
            IsFiniteTypeLocallyConstantModule F)
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        C.IsStrictlyLE n ∧
          (∀ i : ℤ, IsFiniteAffineEtaleExtensionByZeroSum (C.X i)) ∧
            Nonempty (K ≅ DerivedCategory.Q.obj C) := sorry

variable [((X.smallEtaleTopology.W :
  MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive` zeros.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in
/-- A bounded-above derived module sheaf on a quasi-compact and quasi-separated scheme
over a Noetherian coefficient ring has constructible cohomology if and only if it admits
a complex representative with the same upper bound whose terms are tensor-flat
constructible module sheaves. -/
theorem mem_etaleConstructible_iff_iso_flatConstructible
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (n : ℤ) [K.IsLE n] :
    (∀ k : ℤ,
        IsConstructibleEtaleModule
          (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
            (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
            IsFiniteTypeLocallyConstantModule F)
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        C.IsStrictlyLE n ∧
          (∀ i : ℤ,
            IsConstructibleEtaleModule
              (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
                (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
              (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
                IsFiniteTypeLocallyConstantModule F) (C.X i) ∧
              IsFlat (C.X i)) ∧
            Nonempty (K ≅ DerivedCategory.Q.obj C) := sorry

end AlgebraicGeometry.Scheme
