/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarLocalMorphismProperty.Cancellation
import StacksCheckRecall

/-!
# Cancellation of local WAdm^{adic*} morphism properties

If `P` is a local property of morphisms of `WAdm^{adic*}` that has the
cancellation property, then the equivalent conditions of Remark 87.21.4
cancel along postcomposition of morphisms of locally adic* formal algebraic
spaces: `etaleAffineLocally P (f ≫ g)` and `etaleAffineLocally P g` imply
`etaleAffineLocally P f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.17 (Variant for adic-star)
A local property of morphisms of WAdm^{adic*} with cancellation cancels along
postcomposition of morphisms of locally adic-star formal algebraic spaces. -/
@[stacks 0GBN] #check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : IsLocallyAdicStar.etaleAffineLocally P (f ≫ g))
    (hg : IsLocallyAdicStar.etaleAffineLocally P g),
    IsLocallyAdicStar.etaleAffineLocally P f)

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnTarget.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : IsLocallyAdicStar.existsCoverOnTarget P (f ≫ g))
    (hg : IsLocallyAdicStar.existsCoverOnTarget P g),
    IsLocallyAdicStar.existsCoverOnTarget P f)

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnSource.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : IsLocallyAdicStar.existsCoverOnSource P (f ≫ g))
    (hg : IsLocallyAdicStar.existsCoverOnSource P g),
    IsLocallyAdicStar.existsCoverOnSource P f)

#check (TopologicalRing.IsAdicStarRing.HasCancellationProperty :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop) → Prop)
