module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianBaseChange
import StacksCheckRecall

/-!
# Relative base change for locally Noetherian formal algebraic spaces

The ring stability definition and the geometric transfer of its equivalent
local tests are recorded below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy :
  ∀ (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop), Prop)

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

/- Remark 87.21.10 (Another variant for Noetherian): If local properties P
and Q of morphisms of Noetherian adic rings satisfy stability of P under
completed base change by Q, the local tests for f : X ⟶ Y with P and
g : Z ⟶ Y with Q transfer to the second projection X ×_Y Z ⟶ Z with P. -/
@[stacks 0GBG] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.pullback_snd_of_stableUnderBaseChangeBy :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z]
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally Q g),
    etaleAffineLocally P (pullback.snd f g))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.of_isPullback_of_stableUnderBaseChangeBy :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z]
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f)
    (hg : etaleAffineLocally Q g),
    etaleAffineLocally P snd)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.pullback_snd_of_stableUnderBaseChangeBy :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z]
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget Q g),
    existsCoverOnTarget P (pullback.snd f g))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.pullback_snd_of_stableUnderBaseChangeBy :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z]
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource Q g),
    existsCoverOnSource P (pullback.snd f g))

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
