module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleResolution
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.Sheaf

universe u v

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive` zeros.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in
/- Lemma 59.76.5 (1): a bounded-above derived étale module object on a
quasi-compact and quasi-separated scheme over a Noetherian ring has constructible
cohomology exactly when it admits an affine extension-by-zero finite-sum resolution. -/
@[stacks 0960] #check
  (AlgebraicGeometry.Scheme.mem_etaleConstructible_iff_iso_jShriekSum :
    ∀ {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
      [CompactSpace X] [QuasiSeparatedSpace X]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
      (n : ℤ) [K.IsLE n],
    (∀ k : ℤ,
        IsConstructibleEtaleModule
          (fun {Y} f ↦ ((Scheme.smallEtalePullback f).sheafPullback
            (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
            IsFiniteTypeLocallyConstantModule F)
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        C.IsStrictlyLE n ∧
          (∀ i : ℤ, IsFiniteAffineEtaleExtensionByZeroSum (C.X i)) ∧
            Nonempty (K ≅ DerivedCategory.Q.obj C))

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- `DerivedCategory.Q` is typed using `Abelian.toPreadditive` zeros.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in
/- Lemma 59.76.5 (2): equivalently, the same derived object admits a
bounded-above resolution by flat constructible étale module sheaves. -/
@[stacks 0960] #check
  (AlgebraicGeometry.Scheme.mem_etaleConstructible_iff_iso_flatConstructible :
    ∀ {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
      [CompactSpace X] [QuasiSeparatedSpace X]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [((X.smallEtaleTopology.W :
        MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
      (n : ℤ) [K.IsLE n],
    (∀ k : ℤ,
        IsConstructibleEtaleModule
          (fun {Y} f ↦ ((Scheme.smallEtalePullback f).sheafPullback
            (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
            IsFiniteTypeLocallyConstantModule F)
          ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) k).obj K)) ↔
      ∃ C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        C.IsStrictlyLE n ∧
          (∀ i : ℤ,
            IsConstructibleEtaleModule
              (fun {Y} f ↦ ((Scheme.smallEtalePullback f).sheafPullback
                (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
              (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
                IsFiniteTypeLocallyConstantModule F) (C.X i) ∧
              IsFlat (C.X i)) ∧
            Nonempty (K ≅ DerivedCategory.Q.obj C))
