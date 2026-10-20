module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Diagonal

/-!
# Diagonal equalizers of contraction triples

The canonical algebraic and formal equalizers, their geometric properties,
and the solution representing the diagonal fiber.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open AlgebraicGeometry.AlgebraicSpace.ContractionSituation

noncomputable section

universe u

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]
variable (ξ1 ξ2 : Triple σ V)
variable (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
variable (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)

#check (DiagonalEqualizer.of ξ1 ξ2 w1 w2 : DiagonalEqualizer ξ1 ξ2 w1 w2)

#check (DiagonalEqualizer.instSeparated_toV ξ1 ξ2 w1 w2 :
    Separated (DiagonalEqualizer.interpToV ξ1 ξ2 w1 w2))

#check (DiagonalEqualizer.instLocallyOfFiniteType_toV ξ1 ξ2 w1 w2 :
    LocallyOfFiniteType (DiagonalEqualizer.interpToV ξ1 ξ2 w1 w2))

#check (DiagonalEqualizer.instIsLocallyNoetherian_space ξ1 ξ2 w1 w2 :
    IsLocallyNoetherian (DiagonalEqualizer.interpSpace ξ1 ξ2 w1 w2))

#check (DiagonalEqualizer.instIsFormal_formal ξ1 ξ2 :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (DiagonalEqualizer.interpFormal ξ1 ξ2))

#check (DiagonalEqualizer.instIsLocallyNoetherian_formal ξ1 ξ2 :
    @FormalAlgebraicSpace.IsLocallyNoetherian _ (DiagonalEqualizer.interpFormal ξ1 ξ2)
      (DiagonalEqualizer.instIsFormal_formal ξ1 ξ2))

#check (DiagonalEqualizer.instSeparated_formal ξ1 ξ2 :
    FormalAlgebraicSpace.Separated (DiagonalEqualizer.interpToOver ξ1 ξ2))

#check (image_inter_subset ξ1 ξ2 w1 w2 :
    Set.range (Points.map (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toV) ∩
        (ξ1.Z ∪ ξ2.Z) ⊆
      (ξ1.Z ⊓ ξ2.Z : Set _))

#check (openRestrict_mono ξ1 ξ2 w1 w2 :
    Mono (DiagonalEqualizer.openPullbackSnd (DiagonalEqualizer.of ξ1 ξ2 w1 w2)) ∧
      DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          openComplementAlong.mapOfLe
            (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
        DiagonalEqualizer.openPullbackSnd
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2) ∧
      IsPullback
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          DiagonalEqualizer.leftOpen ξ1 ξ2)
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2)
        (prod.lift (𝟙 σ.openComplement) (𝟙 σ.openComplement))
        (prod.lift (DiagonalEqualizer.leftOpen ξ1 ξ2)
          (DiagonalEqualizer.rightOpen ξ1 ξ2)))

#check (isPullback_factor ξ1 ξ2 w1 w2 :
    (DiagonalEqualizer.of ξ1 ξ2 w1 w2).factor ≫
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal =
        completionAlong.map (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toV
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed ∧
      IsPullback
        (DiagonalEqualizer.completionSpace ξ1 ξ2 w1 w2)
        (DiagonalEqualizer.of ξ1 ξ2 w1 w2).factor σ.g
        ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal ≫
          DiagonalEqualizer.leftHat ξ1 ξ2))

#check (DiagonalEqualizer.instFormalModification_factor ξ1 ξ2 w1 w2 :
    @FormalAlgebraicSpace.FormalModification S
      (completionAlong (DiagonalEqualizer.interpSpace ξ1 ξ2 w1 w2) (DiagonalEqualizer.spaceClosed ξ1 ξ2 w1 w2)) (DiagonalEqualizer.interpFormal ξ1 ξ2)
      (DiagonalEqualizer.interpFactor ξ1 ξ2 w1 w2)
      (instIsFormalAlgebraicSpace_completionAlong (DiagonalEqualizer.interpSpace ξ1 ξ2 w1 w2) (DiagonalEqualizer.spaceClosed ξ1 ξ2 w1 w2))
      (DiagonalEqualizer.instIsFormal_formal ξ1 ξ2)
      (@instIsLocallyNoetherian_completionAlong S (DiagonalEqualizer.interpSpace ξ1 ξ2 w1 w2)
        (DiagonalEqualizer.instIsLocallyNoetherian_space ξ1 ξ2 w1 w2) (DiagonalEqualizer.spaceClosed ξ1 ξ2 w1 w2))
      (DiagonalEqualizer.instIsLocallyNoetherian_formal ξ1 ξ2) (DiagonalEqualizer.instLocallyOfFiniteType_factor ξ1 ξ2 w1 w2))

#check (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2 : ContractionSituation V.left)

#check (DiagonalEqualizer.toSituation_X' ξ1 ξ2 w1 w2 :
    (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2).X' = DiagonalEqualizer.sliceSpace ξ1 ξ2 w1 w2)

#check (DiagonalEqualizer.toSituation_T' ξ1 ξ2 w1 w2 :
    (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2).T' = DiagonalEqualizer.sliceClosed ξ1 ξ2 w1 w2)

#check (DiagonalEqualizer.toSituation_W ξ1 ξ2 w1 w2 :
    (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2).W = DiagonalEqualizer.sliceFormal ξ1 ξ2 w1 w2)

#check (DiagonalEqualizer.toSituation_g ξ1 ξ2 w1 w2 :
    (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2).g = DiagonalEqualizer.sliceFactor ξ1 ξ2 w1 w2)

#check (restricts_iff_factors ξ1 ξ2 w1 w2 :
    ∀ {A : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V),
    DiagonalEqualizer.agrees ξ1 ξ2 φ ↔
      (∃ h : openComplementAlong (ofOver A)
            ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (AlgebraicSpace.ofOverMap φ))) ⟶
          DiagonalEqualizer.openPullback (DiagonalEqualizer.of ξ1 ξ2 w1 w2),
        h ≫ DiagonalEqualizer.openPullbackSnd
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2) =
          openComplementAlong.map (AlgebraicSpace.ofOverMap φ)
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed) ∧
      (∃ k : completionAlong (ofOver A)
            ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (AlgebraicSpace.ofOverMap φ))) ⟶
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).formal,
        k ≫ (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal =
          completionAlong.map (AlgebraicSpace.ofOverMap φ)
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed))

variable (E : AlgebraicSpace V.left) [LocallyOfFiniteType (toBase E)]
variable (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E)

/- Remark 98.27.7
A solution of the equalizer contraction situation represents the diagonal fiber
on locally Noetherian schemes over the test scheme. -/
@[stacks 0GHD] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.represents_diagonalFiber
    ξ1 ξ2 w1 w2 E sol : IsIso (diagonalFiberHom ξ1 ξ2 w1 w2 E sol))
