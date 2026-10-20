module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.BaseChange
import StacksCheckRecall

/-!
# Base change of local tests of morphisms of locally countably indexed formal algebraic spaces

If `P` is a local property of morphisms of `WAdm^count` which is stable under
base change, then the equivalent tests of Lemma 87.21.3 pass from
`f : X ⟶ Y` to the projection `pullback.snd f g : X ×_Y Z ⟶ Z`.
The chosen-site formulation assumes `ChosenBigSite.IsSizeClosed 𝒮` to express
the ambient big-site convention: bounded-size schemes and countable
coproducts needed for the affine constructions are represented in the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

/- Lemma 87.21.7: Let `S` be a scheme. Let `P` be a local property of morphisms
of `WAdm^count` which is stable under base change. Let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally countably indexed formal algebraic spaces
over `S`. If `f` satisfies the equivalent conditions of Lemma 87.21.3, then so
does `pullback.snd f g : X ×_Y Z ⟶ Z`. The chosen-site size-closure premise
records the ambient big-site convention for the required affine constructions. -/
@[stacks 0GBD] #check (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally.pullback_snd :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f),
    etaleAffineLocally P (pullback.snd f g))

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.etaleAffineLocally.of_isPullback :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyCountablyIndexed W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f),
    etaleAffineLocally P snd)

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnTarget.pullback_snd :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f),
    existsCoverOnTarget P (pullback.snd f g))

#check (AlgebraicGeometry.IsLocallyCountablyIndexed.existsCoverOnSource.pullback_snd :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop)
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f),
    existsCoverOnSource P (pullback.snd f g))

end AlgebraicGeometry.IsLocallyCountablyIndexed
