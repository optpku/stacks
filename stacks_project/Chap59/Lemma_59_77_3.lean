module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.DerivedCategory
  CategoryTheory.MonoidalCategory CategoryTheory.Sheaf

universe u v

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]
variable [((X.smallEtaleTopology.W :
    MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
-- Local instance justification (defeq pin): derived-category quotients and cochain complexes require the canonical abelian preadditive zero morphisms.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms
variable (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
variable (a b : ℤ)

/- Lemma 59.77.3 (1): constructible Tor-finite objects are represented by bounded
constructible-flat complexes. -/
@[stacks 03TT] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.constructibleTorFinite_iff_exists_constructibleFlatComplex
    (X := X) (Λ := Λ) K :
      constructibleTorFinite X Λ K ↔
        ∃ F : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
          Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ constructibleFlatComplex X Λ F)

/- Lemma 59.77.3 (2): the equivalent interval formulation gives a representative strictly
supported in `[a, b]` from constructible cohomology and a flat representative in `[a, b]`. -/
@[stacks 03TT] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.exists_constructibleFlatComplex_of_hasFlatRepresentativeIn
    (X := X) (Λ := Λ) K a b :
      (∀ degree : ℤ, constructibleModule X Λ
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) degree).obj K)) →
      DerivedCategory.HasFlatRepresentativeIn K a b →
      ∃ F : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ,
        Nonempty (DerivedCategory.Q.obj F ≅ K) ∧ F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
          constructibleFlatComplex X Λ F)

end AlgebraicGeometry.Scheme.Etale.Derived
