module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Convolution

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 56.5.9: if `X` and `Y` are quasi-compact with affine diagonal, then the
`R`-linear exact coproduct-preserving functors
`F : Scheme.QCoh X ⥤ Scheme.QCoh Y` and `G : Scheme.QCoh Y ⥤ Scheme.QCoh Z`
have corresponding kernels `K` on `X ×_R Y` and `L` on `Y ×_R Z` by
Lemma 56.5.7, and `F ⋙ G` corresponds to the convolution kernel
`pr₁₃,*(pr₁₂^* K ⊗ pr₂₃^* L)` on `X ×_R Z`. -/
@[stacks 0GPC] #check
  (AlgebraicGeometry.Scheme.QCoh.fourierMukaiKernel_comp :
    ∀ {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      (z : Z ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [CompactSpace Y]
      [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
      (F : Scheme.QCoh X ⥤ Scheme.QCoh Y)
      (G : Scheme.QCoh Y ⥤ Scheme.QCoh Z)
      [Scheme.QCoh.ExactAdmissible x y F] [Scheme.QCoh.ExactAdmissible y z G]
      (K : Scheme.QCoh (Limits.pullback x y))
      (L : Scheme.QCoh (Limits.pullback y z)),
      Nonempty (F ≅ Scheme.QCoh.fourierMukai x y K) →
      Nonempty (G ≅ Scheme.QCoh.fourierMukai y z L) →
      Nonempty (F ⋙ G ≅
        Scheme.QCoh.fourierMukai x z (Scheme.QCoh.composeKernel x y z K L)))
