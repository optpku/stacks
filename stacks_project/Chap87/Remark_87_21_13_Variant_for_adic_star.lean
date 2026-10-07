module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_Local
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_MorphismProperty
public import stacks_project.Chap87.Remark_87_21_13_Variant_for_adic_star_Composition
import StacksCheckRecall

/-!
# Composition of local WAdm^{adic*} morphism properties

If `P` is a local property of morphisms of `WAdm^{adic*}` that is stable under
composition, then the equivalent conditions of the Lemma 87.21.3 variant in
Remark 87.21.4 are stable under composition of morphisms of locally adic*
formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

/- Remark 87.21.13 (Variant for adic-star) (1): a property P of morphisms of
WAdm^{adic*} is stable under composition if given continuous morphisms
φ : B →+* A and ψ : C →+* B of WAdm^{adic*}, P φ and P ψ imply P (φ.comp ψ). -/
@[stacks 0GBJ] #check TopologicalRing.IsAdicStarRing.IsStableUnderComposition

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
    [IsLocallyAdicStar Z]
variable {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Remark 87.21.13 (Variant for adic-star) (2): Let `S` be a scheme. Let `P`
be a local property of morphisms of `WAdm^{adic*}` which is stable under
composition. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally adic*
formal algebraic spaces over `S`. If `f` and `g` satisfy the equivalent
conditions of the Lemma 87.21.3 variant in Remark 87.21.4, then so does
`f ≫ g : X ⟶ Z`. -/
@[stacks 0GBJ]
theorem etaleAffineLocally.comp (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (h_stable : IsAdicStarRing.IsStableUnderComposition P)
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally P g) :
    etaleAffineLocally P (f ≫ g) := sorry

/-- Condition (2) of the Lemma 87.21.3 variant is stable under composition: if
`P` is a local property of morphisms of `WAdm^{adic*}` that is stable under
composition, and `f` and `g` admit Definition 87.11.1 coverings of the target
as in `existsCoverOnTarget`, then so does `f ≫ g`. -/
theorem existsCoverOnTarget.comp (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (h_stable : IsAdicStarRing.IsStableUnderComposition P)
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget P g) :
    existsCoverOnTarget P (f ≫ g) := sorry

/-- Condition (3) of the Lemma 87.21.3 variant is stable under composition: if
`P` is a local property of morphisms of `WAdm^{adic*}` that is stable under
composition, and `f` and `g` admit Definition 87.11.1 coverings of the source
as in `existsCoverOnSource`, then so does `f ≫ g`. -/
theorem existsCoverOnSource.comp (hP : IsAdicStarRing.IsLocalMorphismProperty P)
    (h_stable : IsAdicStarRing.IsStableUnderComposition P)
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource P g) :
    existsCoverOnSource P (f ≫ g) := sorry

end AlgebraicGeometry.IsLocallyAdicStar
