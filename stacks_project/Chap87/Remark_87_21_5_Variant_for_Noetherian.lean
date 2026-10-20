/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty
import StacksCheckRecall

/-!
# Local tests of morphism properties of locally Noetherian formal algebraic spaces

A local property of morphisms of Noetherian adic rings yields three equivalent
étale affine tests for locally Noetherian formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

/- Remark 87.21.5 (Variant for Noetherian): the universal affine étale test,
the target-cover test, and the source-cover test are equivalent for a local
property of morphisms of Noetherian adic rings. -/
@[stacks 0ANI] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.tfae :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (hP : Noetherian.IsLocalMorphismProperty P),
    List.TFAE [etaleAffineLocally P f, existsCoverOnTarget P f,
      existsCoverOnSource P f])

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty :
    (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop) → Prop)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally_iff_existsCoverOnTarget :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (hP : Noetherian.IsLocalMorphismProperty P),
    etaleAffineLocally P f ↔ existsCoverOnTarget P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally_iff_existsCoverOnSource :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (hP : Noetherian.IsLocalMorphismProperty P),
    etaleAffineLocally P f ↔ existsCoverOnSource P f)

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
