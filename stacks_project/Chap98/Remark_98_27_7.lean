module

public import stacks_project.Chap98.Remark_98_27_7_Equalizer

/-!
# Diagonal equalizers of Artin contraction triples

In Situation 98.27.1, two compatible triples on a locally Noetherian scheme
`V` over `S` determine equalizers `E'` and `E_W` whose image, open-mono,
cartesian, contraction-over-`V`, and restriction-equivalence properties
describe the diagonal fibre product of the contraction functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.ContractionSituation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]
variable (ξ1 ξ2 : Triple σ V)
variable (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
variable (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)

/-- The canonical diagonal equalizer of the two triples. -/
def canonicalEqualizer := DiagonalEqualizer.of ξ1 ξ2 w1 w2

/-- Remark 98.27.7 (1): the image of `E' ⟶ V` meets `Z_1 ∪ Z_2` only inside
`Z = Z_1 ∩ Z_2`. -/
@[stacks 0GHD]
theorem image_inter_subset :
    Set.range (Points.map (canonicalEqualizer ξ1 ξ2 w1 w2).toV) ∩
        (ξ1.Z ∪ ξ2.Z) ⊆
      (ξ1.Z ⊓ ξ2.Z : Set _) :=
  sorry

/-- Remark 98.27.7 (2): the morphism `E' ×_V (V \ Z) ⟶ V \ Z` is a
monomorphism, and the induced map `E' ×_V (V \ Z) ⟶ V \ (Z_1 ∪ Z_2)` is the
equalizer of the restrictions of `ξ1.u'` and `ξ2.u'`. -/
@[stacks 0GHD]
theorem openRestrict_mono :
    Mono (DiagonalEqualizer.openPullbackSnd (canonicalEqualizer ξ1 ξ2 w1 w2)) ∧
      DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          openComplementAlong.mapOfLe
            (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
        DiagonalEqualizer.openPullbackSnd
          (canonicalEqualizer ξ1 ξ2 w1 w2) ∧
      IsPullback
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          DiagonalEqualizer.leftOpen ξ1 ξ2)
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2)
        (prod.lift (𝟙 σ.openComplement) (𝟙 σ.openComplement))
        (prod.lift (DiagonalEqualizer.leftOpen ξ1 ξ2)
          (DiagonalEqualizer.rightOpen ξ1 ξ2)) :=
  sorry

/-- Remark 98.27.7 (3): `E'_{/Z} ⟶ V_{/Z}` factors through `E_W` and the square
with `g : X'_{/T'} ⟶ W` is cartesian, so `E'_{/Z} ⟶ E_W` is a formal
modification as a base change of `g`. -/
@[stacks 0GHD]
theorem isPullback_factor :
    (canonicalEqualizer ξ1 ξ2 w1 w2).factor ≫
          (canonicalEqualizer ξ1 ξ2 w1 w2).toFormal =
        completionAlong.map (canonicalEqualizer ξ1 ξ2 w1 w2).toV
          (canonicalEqualizer ξ1 ξ2 w1 w2).closed ∧
      IsPullback
        (DiagonalEqualizer.completionSpace ξ1 ξ2 w1 w2)
        (canonicalEqualizer ξ1 ξ2 w1 w2).factor σ.g
        ((canonicalEqualizer ξ1 ξ2 w1 w2).toFormal ≫
          DiagonalEqualizer.leftHat ξ1 ξ2) :=
  sorry

/-- Remark 98.27.7 (4): `E'`, the inverse image of `Z` along `E' ⟶ V`, and
`E'_{/Z} ⟶ E_W` form a contraction situation with base scheme the locally
Noetherian scheme `V`. -/
@[stacks 0GHD]
def toSituation : ContractionSituation V.left :=
  DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2

/-- The algebraic space of the contraction situation over `V` is `E'` viewed
over `V` via `toV`. -/
theorem toSituation_X' :
    (toSituation ξ1 ξ2 w1 w2).X' = DiagonalEqualizer.sliceSpace ξ1 ξ2 w1 w2 :=
  sorry

/-- The closed subset of the contraction situation over `V` is
`(E' ⟶ V)⁻¹ Z`. -/
theorem toSituation_T' :
    (toSituation ξ1 ξ2 w1 w2).T' = DiagonalEqualizer.sliceClosed ξ1 ξ2 w1 w2 :=
  sorry

/-- The formal algebraic space of the contraction situation over `V` is the
fibre of `E_W`. -/
theorem toSituation_W :
    (toSituation ξ1 ξ2 w1 w2).W = DiagonalEqualizer.sliceFormal ξ1 ξ2 w1 w2 :=
  sorry

/-- The comparison of the contraction situation over `V` is the restriction of
`factor`. -/
theorem toSituation_g :
    (toSituation ξ1 ξ2 w1 w2).g = DiagonalEqualizer.sliceFactor ξ1 ξ2 w1 w2 :=
  sorry

/-- Remark 98.27.7 (5): for a morphism `φ : A ⟶ V` of locally Noetherian schemes
over `S`, the two triples restrict to the same element of `F(A)` if and only if
`A \ φ⁻¹(Z) ⟶ V \ Z` factors through `E' ×_V (V \ Z)` and
`A_{/φ⁻¹(Z)} ⟶ V_{/Z}` factors through `E_W`. -/
@[stacks 0GHD]
theorem restricts_iff_factors {A : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V) :
    DiagonalEqualizer.agrees ξ1 ξ2 φ ↔
      (∃ h : openComplementAlong (ofOver A)
            ((canonicalEqualizer ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (ofOverMap φ))) ⟶
          DiagonalEqualizer.openPullback (canonicalEqualizer ξ1 ξ2 w1 w2),
        h ≫ DiagonalEqualizer.openPullbackSnd
            (canonicalEqualizer ξ1 ξ2 w1 w2) =
          openComplementAlong.map (ofOverMap φ)
            (canonicalEqualizer ξ1 ξ2 w1 w2).closed) ∧
      (∃ k : completionAlong (ofOver A)
            ((canonicalEqualizer ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (ofOverMap φ))) ⟶
          (canonicalEqualizer ξ1 ξ2 w1 w2).formal,
        k ≫ (canonicalEqualizer ξ1 ξ2 w1 w2).toFormal =
          completionAlong.map (ofOverMap φ)
            (canonicalEqualizer ξ1 ξ2 w1 w2).closed) :=
  sorry

/-- A morphism into a solution over `V` forces the two triples to agree. -/
theorem agrees_of_solutionHom (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (toSituation ξ1 ξ2 w1 w2) E)
    {A : (locallyNoetherian V.left).FullSubcategory}
    (f : ofOver A.obj ⟶ E) :
    DiagonalEqualizer.agrees ξ1 ξ2 (overHom V A.obj) :=
  sorry

/-- The comparison from morphisms into a solution to agreement of the two
triples, on locally Noetherian schemes over `V`. -/
def diagonalFiberHom (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (toSituation ξ1 ξ2 w1 w2) E) :
    homOnLocallyNoetherian E ⟶ DiagonalEqualizer.agreesFunctor ξ1 ξ2 where
  app A := ofHom fun f ↦ ⟨⟨agrees_of_solutionHom ξ1 ξ2 w1 w2 E sol f⟩⟩
  naturality := sorry

/-- Remark 98.27.7 (6): if `E ⟶ V` is a solution for the contraction situation of
(4), then `E` represents `F ×_{Δ, F × F} V` on locally Noetherian schemes over
`V`. -/
@[stacks 0GHD]
theorem represents_diagonalFiber (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (toSituation ξ1 ξ2 w1 w2) E) :
    IsIso (diagonalFiberHom ξ1 ξ2 w1 w2 E sol) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
