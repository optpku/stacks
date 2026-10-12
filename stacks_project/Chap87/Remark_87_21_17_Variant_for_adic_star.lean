/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star
public import stacks_project.Chap87.Remark_87_21_17_Variant_for_adic_star_Cancellation
import StacksCheckRecall

/-!
# Cancellation of local WAdm^{adic*} morphism properties

If `P` is a local property of morphisms of `WAdm^{adic*}` that has the
cancellation property, then the equivalent conditions of Remark 87.21.4
cancel along postcomposition of morphisms of locally adic* formal algebraic
spaces: `etaleAffineLocally P (f ≫ g)` and `etaleAffineLocally P g` imply
`etaleAffineLocally P f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.17 (Variant for adic-star) (1): a local property P of morphisms of
WAdm^{adic*} has the cancellation property when, for morphisms B → A and C → B,
P(C → B) and P(C → A) imply P(B → A). -/
@[stacks 0GBN] #check TopologicalRing.IsAdicStarRing.HasCancellationProperty

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]
    [IsLocallyAdicStar Z]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Remark 87.21.17 (Variant for adic-star) (2): Let `S` be a scheme. Let `P`
be a local property of morphisms of `WAdm^{adic*}` which has the cancellation
property. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally adic*
formal algebraic spaces over `S`. If `f ≫ g` and `g` satisfy the equivalent
conditions of Remark 87.21.4 (`etaleAffineLocally`, `existsCoverOnTarget`,
and `existsCoverOnSource`), then so does `f : X ⟶ Y`. -/
@[stacks 0GBN]
theorem etaleAffineLocally.of_comp (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : etaleAffineLocally P (f ≫ g)) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P f := sorry

/-- Condition (2) of the adic* variant of Lemma 87.21.3 cancels along
postcomposition: if `P` is a local property of morphisms of `WAdm^{adic*}` with
the cancellation property, and `f ≫ g` and `g` admit Definition 87.11.1
coverings of the target as in `existsCoverOnTarget`, then so does `f`. -/
theorem existsCoverOnTarget.of_comp (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : existsCoverOnTarget P (f ≫ g)) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P f := sorry

/-- Condition (3) of the adic* variant of Lemma 87.21.3 cancels along
postcomposition: if `P` is a local property of morphisms of `WAdm^{adic*}` with
the cancellation property, and `f ≫ g` and `g` admit Definition 87.11.1
coverings of the source as in `existsCoverOnSource`, then so does `f`. -/
theorem existsCoverOnSource.of_comp (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (hCancel : IsAdicStarRing.HasCancellationProperty P)
    (hgf : existsCoverOnSource P (f ≫ g)) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsLocallyAdicStar
