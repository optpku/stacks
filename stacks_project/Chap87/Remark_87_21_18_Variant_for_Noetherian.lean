module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian
public import stacks_project.Chap87.Remark_87_21_18_Variant_for_Noetherian_Cancellation
import StacksCheckRecall

/-!
# Cancellation of local WAdm^Noeth morphism properties

If `P` is a local property of morphisms of `WAdm^Noeth` that has the
cancellation property, then the equivalent conditions of Remark 87.21.5
cancel along postcomposition of morphisms of locally Noetherian formal
algebraic spaces: `etaleAffineLocally P (f ≫ g)` and `etaleAffineLocally P g`
imply `etaleAffineLocally P f`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.18 (Variant for Noetherian) (1): a local property P of morphisms of
WAdm^Noeth has the cancellation property when, for morphisms B → A and C → B,
P(C → B) and P(C → A) imply P(B → A). -/
@[stacks 0GBP] #check TopologicalRing.Noetherian.HasCancellationProperty

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Remark 87.21.18 (Variant for Noetherian) (2): Let `S` be a scheme. Let `P`
be a local property of morphisms of `WAdm^Noeth` which has the cancellation
property. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian
formal algebraic spaces over `S`. If `f ≫ g` and `g` satisfy the equivalent
conditions of Remark 87.21.5 (`etaleAffineLocally`, `existsCoverOnTarget`,
and `existsCoverOnSource`), then so does `f : X ⟶ Y`. -/
@[stacks 0GBP]
theorem etaleAffineLocally.of_comp (hP : Noetherian.IsLocalMorphismProperty P)
    (hCancel : Noetherian.HasCancellationProperty P)
    (hgf : etaleAffineLocally P (f ≫ g)) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P f := sorry

/-- Condition (2) of the Noetherian variant of Lemma 87.21.3 cancels along
postcomposition: if `P` is a local property of morphisms of `WAdm^Noeth` with
the cancellation property, and `f ≫ g` and `g` admit Definition 87.11.1
coverings of the target as in `existsCoverOnTarget`, then so does `f`. -/
theorem existsCoverOnTarget.of_comp (hP : Noetherian.IsLocalMorphismProperty P)
    (hCancel : Noetherian.HasCancellationProperty P)
    (hgf : existsCoverOnTarget P (f ≫ g)) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P f := sorry

/-- Condition (3) of the Noetherian variant of Lemma 87.21.3 cancels along
postcomposition: if `P` is a local property of morphisms of `WAdm^Noeth` with
the cancellation property, and `f ≫ g` and `g` admit Definition 87.11.1
coverings of the source as in `existsCoverOnSource`, then so does `f`. -/
theorem existsCoverOnSource.of_comp (hP : Noetherian.IsLocalMorphismProperty P)
    (hCancel : Noetherian.HasCancellationProperty P)
    (hgf : existsCoverOnSource P (f ≫ g)) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P f := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
