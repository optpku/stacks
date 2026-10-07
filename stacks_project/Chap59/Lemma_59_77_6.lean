module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v r

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Z : Scheme.{u}) (U : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : Y.Etale, Abelian (Sheaf (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory.{r} (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : Y.Etale,
  HasDerivedCategory.{r} (Sheaf (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]
variable [∀ U : Y.Etale, ((Y.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]

/- Lemma 59.77.6: over a Noetherian ring, derived inverse image along any scheme
morphism preserves constructible cohomology and locally finite Tor dimension. -/
@[stacks 0963] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.inverseImage_mem_constructibleTorFinite :
    ∀ (f : X ⟶ Y)
      [hAdd : @CategoryTheory.Functor.Additive
        (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) _ _
        Abelian.toPreadditive Abelian.toPreadditive
        (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
      [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
      [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
      (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))),
      Etale.Derived.constructibleTorFinite Y Λ K →
        Etale.Derived.constructibleTorFinite X Λ
          ((AlgebraicGeometry.Scheme.smallEtaleInverseImageDerived f).obj K))

end AlgebraicGeometry.Scheme
