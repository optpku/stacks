/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_Local
public import stacks_project.Chap87.Remark_87_21_10_Another_variant_for_Noetherian_BaseChange
import StacksCheckRecall

/-!
# Base change by Q of local tests of morphisms of locally Noetherian formal algebraic spaces

Remark 87.21.10 records that a local property `P` of morphisms of
`WAdm^Noeth` is stable under base change by a local property `Q` when
`P (algebraMap B A)` and `Q (algebraMap B C)` imply that `Completed B A C`
is adic Noetherian and that `P (includeRight B A C)`, and that the same
argument as Lemma 87.21.7 then transfers the equivalent local tests from
`f : X ⟶ Y` with `P` and `g : Z ⟶ Y` with `Q` to
`pullback.snd f g : X ×_Y Z ⟶ Z` with `P`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.10 (Another variant for Noetherian) (1): local properties P
and Q of morphisms of WAdm^Noeth satisfy that P is stable under base change
by Q when P(B → A) and Q(B → C) imply both that A ⊗̂_B C is adic Noetherian
and that P(C → A ⊗̂_B C). -/
@[stacks 0GBG] #check TopologicalRing.Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [IsLocallyNoetherian Z]

/-- Remark 87.21.10 (Another variant for Noetherian) (2): Let `S` be a scheme.
Let `P` and `Q` be local properties of morphisms of `WAdm^Noeth` such that
`P` is stable under base change by `Q`. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f`
satisfies the equivalent conditions of the Noetherian variant of
Lemma 87.21.3 for `P` and `g` satisfies them for `Q`, then so does
`pullback.snd f g : X ×_Y Z ⟶ Z` for `P`. -/
@[stacks 0GBG]
theorem etaleAffineLocally.pullback_snd
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally Q g) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- If `IsPullback fst snd f g`, `f` satisfies `etaleAffineLocally P`, and
`g` satisfies `etaleAffineLocally Q`, then the base-change leg `snd`
satisfies `etaleAffineLocally P`. -/
theorem etaleAffineLocally.of_isPullback
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f)
    (hg : etaleAffineLocally Q g) :
    etaleAffineLocally P snd := sorry

/-- If `f` satisfies the covering-on-target test of the Noetherian variant of
Lemma 87.21.3 for `P` and `g` satisfies it for `Q`, then so does
`pullback.snd f g` for `P`. -/
theorem existsCoverOnTarget.pullback_snd
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget Q g) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- If `f` satisfies the covering-on-source test of the Noetherian variant of
Lemma 87.21.3 for `P` and `g` satisfies it for `Q`, then so does
`pullback.snd f g` for `P`. -/
theorem existsCoverOnSource.pullback_snd
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource Q g) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
