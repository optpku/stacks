/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty.Cancellation
import StacksCheckRecall

/-!
# Cancellation of local WAdm^count morphism properties

If `P` is a local property of morphisms of `WAdm^count` that has the
cancellation property, then the equivalent conditions of Lemma 87.21.3
cancel along postcomposition of morphisms of locally countably indexed
formal algebraic spaces: `etaleAffineLocally P (f ≫ g)` and
`etaleAffineLocally P g` imply `etaleAffineLocally P f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing
open AlgebraicGeometry.IsLocallyCountablyIndexed

universe u v

/- Lemma 87.21.16: Let `S` be a scheme. Let `P` be a local property of
morphisms of `WAdm^count` which has the cancellation property. Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally countably indexed
formal algebraic spaces over `S`. If `f ≫ g` and `g` satisfy the equivalent
conditions of Lemma 87.21.3 (`etaleAffineLocally`, `existsCoverOnTarget`,
and `existsCoverOnSource`), then so does `f : X ⟶ Y`. -/
@[stacks 0GBM] #check (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    IsLocalMorphismProperty P → HasCancellationProperty P →
    etaleAffineLocally P (f ≫ g) → etaleAffineLocally P g → etaleAffineLocally P f)

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnTarget.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    IsLocalMorphismProperty P → HasCancellationProperty P →
    existsCoverOnTarget P (f ≫ g) → existsCoverOnTarget P g → existsCoverOnTarget P f)

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnSource.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    IsLocalMorphismProperty P → HasCancellationProperty P →
    existsCoverOnSource P (f ≫ g) → existsCoverOnSource P g → existsCoverOnSource P f)
