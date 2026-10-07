module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.EtaleRootsPullback
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CurveDegree

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

namespace AlgebraicGeometry

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

/-- For a dominant morphism of smooth projective curves, étale `H²` pullback on
`μₙ` is multiplication by the function-field degree under the canonical
`ZMod n` comparison. -/
theorem etaleCohomology_rootsOfUnity_h2_pullback
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : ActualEtaleRootsPullback.rootsOfUnityEtaleAddSheaf Y.left n |>.H 2) :
    ActualEtaleRootsPullback.rootsOfUnityH2Pullback π.left n x =
      (etaleCohomology_rootsOfUnity_h2 X n h_pos h_n).symm
        (SchemeOverField.curveHomDegree π •
          etaleCohomology_rootsOfUnity_h2 Y n h_pos h_n x) := sorry

/-- Under the canonical `H²` comparisons with `ZMod n`, étale pullback is
scalar multiplication by the function-field degree. -/
theorem etaleCohomology_rootsOfUnity_h2_pullback_zmod
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : ActualEtaleRootsPullback.rootsOfUnityEtaleAddSheaf Y.left n |>.H 2) :
    etaleCohomology_rootsOfUnity_h2 X n h_pos h_n
        (ActualEtaleRootsPullback.rootsOfUnityH2Pullback π.left n x) =
      SchemeOverField.curveHomDegree π •
        etaleCohomology_rootsOfUnity_h2 Y n h_pos h_n x := sorry

end AlgebraicGeometry
