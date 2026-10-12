/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_21_3
public import stacks_project.Chap87.Situation_87_21_15_Cancellation

/-!
# Cancellation of local WAdm^count morphism properties

If `P` is a local property of morphisms of `WAdm^count` that has the
cancellation property, then the equivalent conditions of Lemma 87.21.3
cancel along postcomposition of morphisms of locally countably indexed
formal algebraic spaces: `etaleAffineLocally P (f ≫ g)` and
`etaleAffineLocally P g` imply `etaleAffineLocally P f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    [IsLocallyCountablyIndexed Z]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 87.21.16: Let `S` be a scheme. Let `P` be a local property of
morphisms of `WAdm^count` which has the cancellation property. Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally countably indexed
formal algebraic spaces over `S`. If `f ≫ g` and `g` satisfy the equivalent
conditions of Lemma 87.21.3 (`etaleAffineLocally`, `existsCoverOnTarget`,
and `existsCoverOnSource`), then so does `f : X ⟶ Y`. -/
@[stacks 0GBM]
theorem etaleAffineLocally.of_comp (hP : IsLocalMorphismProperty P)
    (hCancel : HasCancellationProperty P)
    (hgf : etaleAffineLocally P (f ≫ g)) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P f := sorry

/-- Condition (2) of Lemma 87.21.3 cancels along postcomposition: if `P` is a
local property of morphisms of `WAdm^count` with the cancellation property,
and `f ≫ g` and `g` admit Definition 87.11.1 coverings of the target as in
`existsCoverOnTarget`, then so does `f`. -/
theorem existsCoverOnTarget.of_comp (hP : IsLocalMorphismProperty P)
    (hCancel : HasCancellationProperty P)
    (hgf : existsCoverOnTarget P (f ≫ g)) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P f := sorry

/-- Condition (3) of Lemma 87.21.3 cancels along postcomposition: if `P` is a
local property of morphisms of `WAdm^count` with the cancellation property,
and `f ≫ g` and `g` admit Definition 87.11.1 coverings of the source as in
`existsCoverOnSource`, then so does `f`. -/
theorem existsCoverOnSource.of_comp (hP : IsLocalMorphismProperty P)
    (hCancel : HasCancellationProperty P)
    (hgf : existsCoverOnSource P (f ≫ g)) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
