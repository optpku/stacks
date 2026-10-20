/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarBaseChange
import StacksCheckRecall

/-!
# Base change of local tests of morphisms of locally adic-star formal algebraic spaces

Completed base-change stability of a local adic-star ring morphism property
transfers to the equivalent affine étale tests on formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing
open AlgebraicGeometry.IsLocallyAdicStar

universe u v

#check (TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop) → Prop)

/- Remark 87.21.8 (Variant for adic-star): a local property of morphisms of
WAdm^{adic*} stable under completed base change induces local tests preserved
by pullback of locally adic-star formal algebraic spaces. -/
@[stacks 0GBE] #check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally.pullback_snd :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f),
    etaleAffineLocally P (pullback.snd f g))

#check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally.of_isPullback :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyAdicStar W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f),
    etaleAffineLocally P snd)

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnTarget.pullback_snd :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f),
    existsCoverOnTarget P (pullback.snd f g))

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnSource.pullback_snd :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyAdicStar X] [IsLocallyAdicStar Y] [IsLocallyAdicStar Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f),
    existsCoverOnSource P (pullback.snd f g))
