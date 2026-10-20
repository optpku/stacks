module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

/-!
# Derivations from pulled-back relative differentials

A linear map out of pulled-back relative differentials determines a relative
derivation with pushed-forward coefficients by adjunction and universal derivation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

/-- The `𝒪_B`-derivation `D = d_{Y/B} ∘ θ` associated to an `𝒪_X`-linear map
`θ : a^* Ω_{Y/B} ⟶ F`, obtained by postcomposing `d_{Y/B}` with the adjunct of
`θ`. -/
def derivationOfPullback {Y B X : AlgebraicSpace S} (hY : Y ⟶ B) (a : X ⟶ Y)
    {F : X.Modules} (θ : (Modules.pullback a).obj (relativeDifferentials hY) ⟶ F) :
    Hom.derivations hY ((Modules.pushforward a).obj F) :=
  (universalDerivation hY).postcomp
    ((SheafOfModules.forget (structureSheaf Y) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf Y).obj)).map
      ((Modules.pullbackPushforwardAdjunction a).homEquiv _ _ θ))

/-- The induced derivation is the universal derivation postcomposed with the
adjunct of the differential parameter. -/
theorem derivationOfPullback_eq {Y B X : AlgebraicSpace S} (hY : Y ⟶ B)
    (a : X ⟶ Y) {F : X.Modules}
    (θ : (Modules.pullback a).obj (relativeDifferentials hY) ⟶ F) :
    derivationOfPullback hY a θ =
      (universalDerivation hY).postcomp
        ((SheafOfModules.forget (structureSheaf Y) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureSheaf Y).obj)).map
          ((Modules.pullbackPushforwardAdjunction a).homEquiv _ _ θ)) :=
  rfl

/-- Universal descent followed by the pullback–pushforward adjunction recovers
the original differential parameter from its induced derivation. -/
theorem derivationOfPullback_spec {Y B X : AlgebraicSpace S} (hY : Y ⟶ B)
    (a : X ⟶ Y) {F : X.Modules}
    (θ : (Modules.pullback a).obj (relativeDifferentials hY) ⟶ F) :
    ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F).symm
      (SheafOfModules.RingedSite.relativeDifferentialDesc.{u + 1, u, u}
        (commInverseImageStructureSheafMap hY) (F := (Modules.pushforward a).obj F)
        (derivationOfPullback hY a θ)) = θ := by
  change ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F).symm
    (SheafOfModules.RingedSite.relativeDifferentialDesc.{u + 1, u, u}
      (commInverseImageStructureSheafMap hY)
      (F := (Modules.pushforward a).obj F)
      ((SheafOfModules.RingedSite.relativeDifferential.{u + 1, u, u}
        (commInverseImageStructureSheafMap hY)).postcomp
          (((Modules.pullbackPushforwardAdjunction a).homEquiv
            (Hom.relativeDifferentials hY) F θ).val))) = θ
  exact (congrArg
    ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F).symm
    (SheafOfModules.RingedSite.RelativeDifferentials.desc_postcomp_relativeDifferential
      (commInverseImageStructureSheafMap hY)
      ((Modules.pullbackPushforwardAdjunction a).homEquiv (Hom.relativeDifferentials hY) F θ))).trans
        (Equiv.symm_apply_apply _ θ)

end AlgebraicGeometry.AlgebraicSpace.Hom
