/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.H2PullbackDegree

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {X Y : SchemeOverField k}
variable [Curve X] [Curve Y] [Smooth X.hom] [Smooth Y.hom]
variable [Projective X.hom] [Projective Y.hom]
variable (π : X ⟶ Y) [IsDominant π.left]
variable (n : ℕ)
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ F : (Y.left.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Scheme.smallEtalePullback π.left).op.HasLeftKanExtension F]

/- Lemma 59.69.2: for a nonconstant morphism `π : X ⟶ Y` of smooth projective
curves over an algebraically closed field `k`, and `n ≥ 1` invertible in `k`,
the map `π* : H²_etale(Y, μₙ) ⟶ H²_etale(X, μₙ)` is multiplication by the degree of `π`. -/
@[stacks 0AMB] #check
  (AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2_pullback π n :
    ∀ (h_pos : 0 < n) (h_n : IsUnit (n : k))
      (x : ActualEtaleRootsPullback.rootsOfUnityEtaleAddSheaf Y.left n |>.H 2),
      ActualEtaleRootsPullback.rootsOfUnityH2Pullback π.left n x =
        (AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2 X n h_pos h_n).symm
          (AlgebraicGeometry.SchemeOverField.curveHomDegree π •
            AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2 Y n h_pos h_n x))

/- After the identifications `H²_etale(−, μₙ) ≃+ ZMod n`, pullback along `π`
is scalar multiplication by the degree of `π`. -/
#check
  (AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2_pullback_zmod π n :
    ∀ (h_pos : 0 < n) (h_n : IsUnit (n : k))
      (x : ActualEtaleRootsPullback.rootsOfUnityEtaleAddSheaf Y.left n |>.H 2),
      AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2 X n h_pos h_n
          (ActualEtaleRootsPullback.rootsOfUnityH2Pullback π.left n x) =
        AlgebraicGeometry.SchemeOverField.curveHomDegree π •
          AlgebraicGeometry.etaleCohomology_rootsOfUnity_h2 Y n h_pos h_n x)

end
