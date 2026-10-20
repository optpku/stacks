/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty.Composition
import StacksCheckRecall

/-!
# Composition of local properties of locally Noetherian formal algebraic spaces

Composition stability on Noetherian adic rings induces composition stability
for all three equivalent affine étale local testing formulations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing
open AlgebraicGeometry.IsFormalAlgebraicSpace
open AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

universe u v

/- Remark 87.21.14 (Variant for Noetherian): A local property of morphisms of
Noetherian adic rings stable under composition induces a composition-stable
property of morphisms of locally Noetherian formal algebraic spaces. -/
@[stacks 0GBK] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z},
    Noetherian.IsLocalMorphismProperty P →
    Noetherian.IsStableUnderComposition P →
    etaleAffineLocally P f → etaleAffineLocally P g → etaleAffineLocally P (f ≫ g))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z},
    Noetherian.IsLocalMorphismProperty P →
    Noetherian.IsStableUnderComposition P →
    existsCoverOnTarget P f → existsCoverOnTarget P g → existsCoverOnTarget P (f ≫ g))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z},
    Noetherian.IsLocalMorphismProperty P →
    Noetherian.IsStableUnderComposition P →
    existsCoverOnSource P f → existsCoverOnSource P g → existsCoverOnSource P (f ≫ g))

#check (TopologicalRing.Noetherian.IsStableUnderComposition :
  (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop) → Prop)
