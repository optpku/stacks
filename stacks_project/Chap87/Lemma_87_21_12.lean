/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty.Composition
import StacksCheckRecall

/-!
# Composition of local WAdm^count morphism properties

If `P` is a local property of morphisms of `WAdm^count` that is stable under
composition, then the equivalent conditions of Lemma 87.21.3 are stable under
composition of morphisms of locally countably indexed formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

open AlgebraicGeometry.IsLocallyCountablyIndexed

/- Lemma 87.21.12: A composition-stable local property of morphisms of
countably indexed weakly admissible rings is preserved by composition of
morphisms of locally countably indexed formal algebraic spaces. -/
@[stacks 0GBI]
#check (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z],
    IsLocalMorphismProperty P → IsStableUnderComposition P →
    etaleAffineLocally P f → etaleAffineLocally P g →
    etaleAffineLocally P (f ≫ g))

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnTarget.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z],
    IsLocalMorphismProperty P → IsStableUnderComposition P →
    existsCoverOnTarget P f → existsCoverOnTarget P g →
    existsCoverOnTarget P (f ≫ g))

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnSource.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z],
    IsLocalMorphismProperty P → IsStableUnderComposition P →
    existsCoverOnSource P f → existsCoverOnSource P g →
    existsCoverOnSource P (f ≫ g))
