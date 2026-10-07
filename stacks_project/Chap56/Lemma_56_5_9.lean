module

public import stacks_project.Chap56.Lemma_56_5_9_Convolution

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R]
variable {X Y Z : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R))
variable (y : Y ⟶ Spec (CommRingCat.of R))
variable (z : Z ⟶ Spec (CommRingCat.of R))
variable [CompactSpace X] [CompactSpace Y]
variable [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
variable (F : Scheme.QCoh X ⥤ Scheme.QCoh Y)
variable (G : Scheme.QCoh Y ⥤ Scheme.QCoh Z)
variable [ExactAdmissible x y F] [ExactAdmissible y z G]

/-- Lemma 56.5.9: if `X` and `Y` are quasi-compact with affine diagonal, then the
`R`-linear exact coproduct-preserving functors
`F : Scheme.QCoh X ⥤ Scheme.QCoh Y` and `G : Scheme.QCoh Y ⥤ Scheme.QCoh Z`
have corresponding kernels `K` on `X ×_R Y` and `L` on `Y ×_R Z` by
Lemma 56.5.7, and `F ⋙ G` corresponds to the convolution kernel
`pr₁₃,*(pr₁₂^* K ⊗ pr₂₃^* L)` on `X ×_R Z`. -/
@[stacks 0GPC]
theorem fourierMukaiKernel_comp :
    Nonempty
      (F ⋙ G ≅
        fourierMukai x z
          (composeKernel x y z (fourierMukaiKernel x y F) (fourierMukaiKernel y z G))) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
