/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.AbelianPresentation

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

noncomputable section

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ (n : ℕ) (G : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
  HasCoproduct G]
variable [HasCokernels (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/- Lemma 59.73.7 (1): constructible abelian étale sheaves are cokernels of maps between
finite `ZMod` extension-by-zero sums from quasi-compact and quasi-separated étale objects. -/
@[stacks 09YT] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_iff_exists_coker_zmodExtensionByZero :
    ∀ (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      Sheaf.IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ Sheaf.IsFiniteLocallyConstantAddCommGrp G) F ↔
        ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale)
          (modulusU : Fin n → ℕ) (modulusV : Fin m → ℕ)
          (hPosU : ∀ i, NeZero (modulusU i)) (hPosV : ∀ k, NeZero (modulusV k)),
          (∀ i, CompactSpace (U i).left) ∧
            (∀ i, QuasiSeparatedSpace (U i).left) ∧
              (∀ k, CompactSpace (V k).left) ∧
                (∀ k, QuasiSeparatedSpace (V k).left) ∧
                  ∃ (φ :
                      Sheaf.finiteZModExtensionByZeroSum
                          (hPos := hPosV) (hEtale := fun k ↦ (V k).prop)
                          (hKan := fun k P ↦ hExtension (V k) P) V modulusV ⟶
                        Sheaf.finiteZModExtensionByZeroSum
                          (hPos := hPosU) (hEtale := fun i ↦ (U i).prop)
                          (hKan := fun i P ↦ hExtension (U i) P) U modulusU),
                    Nonempty (F ≅ cokernel φ))

/- Lemma 59.73.7 (2): the same cokernel characterization holds with affine étale objects. -/
@[stacks 09YT] #check
  (CategoryTheory.Sheaf.isConstructibleEtaleAddCommGrp_iff_coker_zmodExtByZero_affine :
    ∀ (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      Sheaf.IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ Sheaf.IsFiniteLocallyConstantAddCommGrp G) F ↔
        ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale)
          (modulusU : Fin n → ℕ) (modulusV : Fin m → ℕ)
          (hPosU : ∀ i, NeZero (modulusU i)) (hPosV : ∀ k, NeZero (modulusV k)),
          (∀ i, IsAffine (U i).left) ∧
            (∀ k, IsAffine (V k).left) ∧
              ∃ (φ :
                  Sheaf.finiteZModExtensionByZeroSum
                      (hPos := hPosV) (hEtale := fun k ↦ (V k).prop)
                      (hKan := fun k P ↦ hExtension (V k) P) V modulusV ⟶
                    Sheaf.finiteZModExtensionByZeroSum
                      (hPos := hPosU) (hEtale := fun i ↦ (U i).prop)
                      (hKan := fun i P ↦ hExtension (U i) P) U modulusU),
                Nonempty (F ≅ cokernel φ))

end
