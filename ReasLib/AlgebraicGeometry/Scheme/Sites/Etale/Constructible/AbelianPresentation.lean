/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.FiniteZModSum
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace CategoryTheory.Sheaf

noncomputable section

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ (n : ℕ) (G : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
  HasCoproduct G]
variable [HasCokernels (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- On a quasi-compact and quasi-separated scheme, a constructible abelian étale sheaf is
exactly a cokernel of a morphism between finite coproducts of constant `ZMod` sheaves extended
by zero from quasi-compact and quasi-separated étale objects, with positive moduli. -/
theorem isConstructibleEtaleAddCommGrp_iff_exists_coker_zmodExtensionByZero
    (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F ↔
      ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale)
        (modulusU : Fin n → ℕ) (modulusV : Fin m → ℕ)
        (hPosU : ∀ i, NeZero (modulusU i)) (hPosV : ∀ k, NeZero (modulusV k)),
        (∀ i, CompactSpace (U i).left) ∧
          (∀ i, QuasiSeparatedSpace (U i).left) ∧
            (∀ k, CompactSpace (V k).left) ∧
              (∀ k, QuasiSeparatedSpace (V k).left) ∧
                ∃ (φ :
                    finiteZModExtensionByZeroSum
                        (hPos := hPosV) (hEtale := fun k ↦ (V k).prop)
                        (hKan := fun k P ↦ hExtension (V k) P) V modulusV ⟶
                      finiteZModExtensionByZeroSum
                        (hPos := hPosU) (hEtale := fun i ↦ (U i).prop)
                        (hKan := fun i P ↦ hExtension (U i) P) U modulusU),
                  Nonempty (F ≅ cokernel φ) := sorry

/-- On a quasi-compact and quasi-separated scheme, a constructible abelian étale sheaf is
exactly a cokernel of a morphism between finite coproducts of constant `ZMod` sheaves extended
by zero from affine étale objects, with positive moduli. -/
theorem isConstructibleEtaleAddCommGrp_iff_coker_zmodExtByZero_affine
    (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F ↔
      ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale)
        (modulusU : Fin n → ℕ) (modulusV : Fin m → ℕ)
        (hPosU : ∀ i, NeZero (modulusU i)) (hPosV : ∀ k, NeZero (modulusV k)),
        (∀ i, IsAffine (U i).left) ∧
          (∀ k, IsAffine (V k).left) ∧
            ∃ (φ :
                finiteZModExtensionByZeroSum
                    (hPos := hPosV) (hEtale := fun k ↦ (V k).prop)
                    (hKan := fun k P ↦ hExtension (V k) P) V modulusV ⟶
                  finiteZModExtensionByZeroSum
                    (hPos := hPosU) (hEtale := fun i ↦ (U i).prop)
                    (hKan := fun i P ↦ hExtension (U i) P) U modulusU),
              Nonempty (F ≅ cokernel φ) := sorry

end

end CategoryTheory.Sheaf
