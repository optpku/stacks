module

public import stacks_project.Chap87.Lemma_87_21_3
public import stacks_project.Chap87.Situation_87_21_11_Composition

/-!
# Composition of local WAdm^count morphism properties

If `P` is a local property of morphisms of `WAdm^count` that is stable under
composition, then the equivalent conditions of Lemma 87.21.3 are stable under
composition of morphisms of locally countably indexed formal algebraic spaces.
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
    [IsLocallyCountablyIndexed Z]
variable {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Lemma 87.21.12: Let `S` be a scheme. Let `P` be a local property of
morphisms of `WAdm^count` which is stable under composition. Let `f : X ⟶ Y`
and `g : Y ⟶ Z` be morphisms of locally countably indexed formal algebraic
spaces over `S`. If `f` and `g` satisfy the equivalent conditions of Lemma
87.21.3, then so does `f ≫ g : X ⟶ Z`. -/
@[stacks 0GBI]
theorem etaleAffineLocally.comp (hP : IsLocalMorphismProperty P)
    (h_stable : IsStableUnderComposition P)
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P (f ≫ g) := sorry

/-- Condition (2) of Lemma 87.21.3 is stable under composition: if `P` is a
local property of morphisms of `WAdm^count` that is stable under composition,
and `f` and `g` admit Definition 87.11.1 coverings of the target as in
`existsCoverOnTarget`, then so does `f ≫ g`. -/
theorem existsCoverOnTarget.comp (hP : IsLocalMorphismProperty P)
    (h_stable : IsStableUnderComposition P)
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P (f ≫ g) := sorry

/-- Condition (3) of Lemma 87.21.3 is stable under composition: if `P` is a
local property of morphisms of `WAdm^count` that is stable under composition,
and `f` and `g` admit Definition 87.11.1 coverings of the source as in
`existsCoverOnSource`, then so does `f ≫ g`. -/
theorem existsCoverOnSource.comp (hP : IsLocalMorphismProperty P)
    (h_stable : IsStableUnderComposition P)
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P (f ≫ g) := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
