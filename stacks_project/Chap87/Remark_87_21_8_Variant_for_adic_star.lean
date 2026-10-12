/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_20_10
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_Local
public import stacks_project.Chap87.Remark_87_21_8_Variant_for_adic_star_Completed
public import stacks_project.Chap87.Remark_87_21_8_Variant_for_adic_star_BaseChange
import StacksCheckRecall

/-!
# Base change of local tests of morphisms of locally adic* formal algebraic spaces

Remark 87.21.8 records that a local property `P` of morphisms of
`WAdm^{adic*}` is stable under base change when `P (algebraMap B A)` implies
`P (includeRight B A C)`, which is well-defined because `Completed B A C`
remains in `WAdm^{adic*}` by Lemma 87.4.12, and that the same argument as
Lemma 87.21.7 then transfers the equivalent local tests to
`pullback.snd f g` for morphisms of locally adic* formal algebraic spaces
over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.8 (Variant for adic-star) (1): a local property P of morphisms
of WAdm^{adic*} is stable under base change when P(B → A) implies
P(C → A ⊗̂_B C). This is well-defined because A ⊗̂_B C remains in
WAdm^{adic*} by Lemma 87.4.12. -/
@[stacks 0GBE] #check TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]
variable [IsLocallyAdicStar Z]

/-- Remark 87.21.8 (Variant for adic-star) (2): Let `S` be a scheme. Let `P`
be a local property of morphisms of `WAdm^{adic*}` which is stable under
base change. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally adic*
formal algebraic spaces over `S`. If `f` satisfies the equivalent conditions
of the adic* variant of Lemma 87.21.3, then so does
`pullback.snd f g : X ×_Y Z ⟶ Z`. -/
@[stacks 0GBE]
theorem etaleAffineLocally.pullback_snd
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- If `IsPullback fst snd f g` and `f` satisfies `etaleAffineLocally P`, then
the base-change leg `snd` satisfies `etaleAffineLocally P`. -/
theorem etaleAffineLocally.of_isPullback
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyAdicStar W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f) :
    etaleAffineLocally P snd := sorry

/-- If `f` satisfies the covering-on-target test of the adic* variant of
Lemma 87.21.3, then so does `pullback.snd f g`. -/
theorem existsCoverOnTarget.pullback_snd
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- If `f` satisfies the covering-on-source test of the adic* variant of
Lemma 87.21.3, then so does `pullback.snd f g`. -/
theorem existsCoverOnSource.pullback_snd
    (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hbc : IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsLocallyAdicStar
