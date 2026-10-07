module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_Local
public import stacks_project.Chap87.Remark_87_21_9_Variant_for_Noetherian_BaseChange
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

/- Remark 87.21.9 (Variant for Noetherian) (1): a local property P of
morphisms of WAdm^Noeth is stable under base change when P(B → A) implies
both that A ⊗̂_B C is adic Noetherian (see Lemma 87.4.12 for a criterion)
and that P(C → A ⊗̂_B C). -/
@[stacks 0GBF] #check TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange

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

/-- Remark 87.21.9 (Variant for Noetherian) (2): Let `S` be a scheme. Let `P`
be a local property of morphisms of `WAdm^Noeth` which is stable under base
change. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally Noetherian
formal algebraic spaces over `S`. If `f` satisfies the equivalent conditions
of the Noetherian variant of Lemma 87.21.3, then so does
`pullback.snd f g : X ×_Y Z ⟶ Z`. -/
@[stacks 0GBF]
theorem etaleAffineLocally.pullback_snd
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- If `IsPullback fst snd f g` and `f` satisfies `etaleAffineLocally P`, then
the base-change leg `snd` satisfies `etaleAffineLocally P`. -/
theorem etaleAffineLocally.of_isPullback
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f) :
    etaleAffineLocally P snd := sorry

/-- If `f` satisfies the covering-on-target test of the Noetherian variant of
Lemma 87.21.3, then so does `pullback.snd f g`. -/
theorem existsCoverOnTarget.pullback_snd
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- If `f` satisfies the covering-on-source test of the Noetherian variant of
Lemma 87.21.3, then so does `pullback.snd f g`. -/
theorem existsCoverOnSource.pullback_snd
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
