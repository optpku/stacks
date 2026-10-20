module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty.Composition
import StacksCheckRecall

/-!
# Composition of local morphism properties of locally adic-star spaces

A composition-stable local property of continuous homomorphisms of adic-star
rings is preserved by composition of morphisms of locally adic-star formal
algebraic spaces, in each affine étale and covering formulation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.13 (Variant for adic-star): a composition-stable local property
of continuous homomorphisms of adic-star rings induces a composition-stable
property of morphisms of locally adic-star formal algebraic spaces. -/
@[stacks 0GBJ] #check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z],
    ChosenBigSite.IsSizeClosed 𝒮 →
    IsAdicStarRing.IsLocalMorphismProperty P →
    IsAdicStarRing.IsStableUnderComposition P →
    IsLocallyAdicStar.etaleAffineLocally P f →
    IsLocallyAdicStar.etaleAffineLocally P g →
    IsLocallyAdicStar.etaleAffineLocally P (f ≫ g))

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnTarget.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z],
    ChosenBigSite.IsSizeClosed 𝒮 →
    IsAdicStarRing.IsLocalMorphismProperty P →
    IsAdicStarRing.IsStableUnderComposition P →
    IsLocallyAdicStar.existsCoverOnTarget P f →
    IsLocallyAdicStar.existsCoverOnTarget P g →
    IsLocallyAdicStar.existsCoverOnTarget P (f ≫ g))

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnSource.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z],
    ChosenBigSite.IsSizeClosed 𝒮 →
    IsAdicStarRing.IsLocalMorphismProperty P →
    IsAdicStarRing.IsStableUnderComposition P →
    IsLocallyAdicStar.existsCoverOnSource P f →
    IsLocallyAdicStar.existsCoverOnSource P g →
    IsLocallyAdicStar.existsCoverOnSource P (f ≫ g))

#check (TopologicalRing.IsAdicStarRing.IsStableUnderComposition :
  (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop) → Prop)

