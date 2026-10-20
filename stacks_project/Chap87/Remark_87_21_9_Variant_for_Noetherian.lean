/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianBaseChange
import StacksCheckRecall

/-!
# Base change of local tests of morphisms of locally Noetherian formal algebraic spaces

Remark 87.21.9 records that a local property `P` of morphisms of
`WAdm^Noeth` is stable under base change when `P (algebraMap B A)` implies
that `Completed B A C` is adic Noetherian and that `P (includeRight B A C)`,
and that the same argument as Lemma 87.21.7 then transfers the equivalent
local tests to `pullback.snd f g` for morphisms of locally Noetherian formal
algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [IsLocallyNoetherian Z]

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P : Prop)

/- Remark 87.21.9 (Variant for Noetherian): a local property stable under
completed base change is preserved by the second pullback projection for
locally Noetherian formal algebraic spaces over a size-closed chosen site. -/
@[stacks 0GBF] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.pullback_snd P :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f),
    etaleAffineLocally P (pullback.snd f g))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.of_isPullback P :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f),
    etaleAffineLocally P snd)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.pullback_snd P :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f),
    existsCoverOnTarget P (pullback.snd f g))

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.pullback_snd P :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f),
    existsCoverOnSource P (pullback.snd f g))

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
