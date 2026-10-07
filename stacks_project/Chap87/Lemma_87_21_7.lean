module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_20_10
public import stacks_project.Chap87.Lemma_87_21_3
public import stacks_project.Chap87.Situation_87_21_6_BaseChange

/-!
# Base change of local tests of morphisms of locally countably indexed formal algebraic spaces

If `P` is a local property of morphisms of `WAdm^count` which is stable under
base change, then the equivalent tests of Lemma 87.21.3 pass from
`f : X ⟶ Y` to the projection `pullback.snd f g : X ×_Y Z ⟶ Z`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
variable [IsLocallyCountablyIndexed Z]

/-- Lemma 87.21.7: Let `S` be a scheme. Let `P` be a local property of morphisms
of `WAdm^count` which is stable under base change. Let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally countably indexed formal algebraic spaces
over `S`. If `f` satisfies the equivalent conditions of Lemma 87.21.3, then so
does `pullback.snd f g : X ×_Y Z ⟶ Z`. Transferring `etaleAffineLocally P f`
also transfers the equivalent covering tests `existsCoverOnTarget` and
`existsCoverOnSource`. -/
@[stacks 0GBD]
theorem etaleAffineLocally.pullback_snd (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- If `IsPullback fst snd f g` and `f` satisfies `etaleAffineLocally P`, then
the base-change leg `snd` satisfies `etaleAffineLocally P`. -/
theorem etaleAffineLocally.of_isPullback (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyCountablyIndexed W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f) :
    etaleAffineLocally P snd := sorry

/-- If `f` satisfies the covering-on-target test of Lemma 87.21.3, then so does
`pullback.snd f g`. -/
theorem existsCoverOnTarget.pullback_snd (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- If `f` satisfies the covering-on-source test of Lemma 87.21.3, then so does
`pullback.snd f g`. -/
theorem existsCoverOnSource.pullback_snd (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
