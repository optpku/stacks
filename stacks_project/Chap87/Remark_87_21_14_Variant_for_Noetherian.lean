module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_5_Variant_for_Noetherian_Local
public import stacks_project.Chap87.Remark_87_21_14_Variant_for_Noetherian_Composition
import StacksCheckRecall

/-!
# Composition of local WAdm^Noeth morphism properties

If `P` is a local property of morphisms of `WAdm^Noeth` that is stable under
composition, then the equivalent conditions of the Noetherian variant of
Lemma 87.21.3 are stable under composition of morphisms of locally Noetherian
formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.14 (Variant for Noetherian) (1): a property P of morphisms of
WAdm^Noeth is stable under composition if given continuous morphisms
φ : B →+* A and ψ : C →+* B of WAdm^Noeth, P φ and P ψ imply P (φ.comp ψ). -/
@[stacks 0GBK] #check TopologicalRing.Noetherian.IsStableUnderComposition

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
    [IsLocallyNoetherian Z]
variable {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Remark 87.21.14 (Variant for Noetherian) (2): Let `S` be a scheme. Let `P`
be a local property of morphisms of `WAdm^Noeth` which is stable under
composition. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally
Noetherian formal algebraic spaces over `S`. If `f` and `g` satisfy the
equivalent conditions of the Noetherian variant of Lemma 87.21.3, then so
does `f ≫ g : X ⟶ Z`. -/
@[stacks 0GBK]
theorem etaleAffineLocally.comp (hP : Noetherian.IsLocalMorphismProperty P)
    (h_stable : Noetherian.IsStableUnderComposition P)
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P (f ≫ g) := sorry

/-- Condition (2) of the Noetherian variant of Lemma 87.21.3 is stable under
composition: if `P` is a local property of morphisms of `WAdm^Noeth` that is
stable under composition, and `f` and `g` admit Definition 87.11.1 coverings
of the target as in `existsCoverOnTarget`, then so does `f ≫ g`. -/
theorem existsCoverOnTarget.comp (hP : Noetherian.IsLocalMorphismProperty P)
    (h_stable : Noetherian.IsStableUnderComposition P)
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P (f ≫ g) := sorry

/-- Condition (3) of the Noetherian variant of Lemma 87.21.3 is stable under
composition: if `P` is a local property of morphisms of `WAdm^Noeth` that is
stable under composition, and `f` and `g` admit Definition 87.11.1 coverings
of the source as in `existsCoverOnSource`, then so does `f ≫ g`. -/
theorem existsCoverOnSource.comp (hP : Noetherian.IsLocalMorphismProperty P)
    (h_stable : Noetherian.IsStableUnderComposition P)
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P (f ≫ g) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
