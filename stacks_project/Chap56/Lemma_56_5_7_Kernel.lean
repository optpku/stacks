module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.ExactKernel
public import stacks_project.Chap56.«56_5_1_1_FourierMukai»
public import stacks_project.Chap56.Lemma_56_5_5
public import stacks_project.Chap56.Lemma_56_5_7_ExactAdmissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable [HasInjectiveResolutions (Limits.pullback x y).Modules]

/- The exact-kernel API is owned by the quasicoherent Fourier--Mukai library. -/
#check (AlgebraicGeometry.Scheme.QCoh.tensorPullback x y :
  Scheme.QCoh (Limits.pullback x y) → Scheme.QCoh X → (Limits.pullback x y).Modules)
#check (AlgebraicGeometry.Scheme.QCoh.higherDirectImage_tensor x y :
  Scheme.QCoh (Limits.pullback x y) → Scheme.QCoh X → ℕ → Y.Modules)
#check (AlgebraicGeometry.Scheme.QCoh.IsExactFourierMukaiKernel x y :
  Scheme.QCoh (Limits.pullback x y) → Prop)
#check (AlgebraicGeometry.Scheme.QCoh.isExactFourierMukaiKernel_iff x y :
  ∀ K : Scheme.QCoh (Limits.pullback x y),
    IsExactFourierMukaiKernel x y K ↔
      Scheme.Modules.flatOver ((inclusion _).obj K) (Limits.pullback.fst x y) ∧
        ∀ (F : Scheme.QCoh X) (q : ℕ), 0 < q →
          IsZero (higherDirectImage_tensor x y K F q))
#check (AlgebraicGeometry.Scheme.QCoh.higherDirectImage_tensor_isZero x y :
  ∀ (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K]
    (F : Scheme.QCoh X) (q : ℕ), 0 < q →
    IsZero (higherDirectImage_tensor x y K F q))
#check (AlgebraicGeometry.Scheme.QCoh.exactFourierMukaiKernel x y : Type (u + 1))
#check (AlgebraicGeometry.Scheme.QCoh.fourierMukai_exactAdmissible x y :
  ∀ [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K],
    ExactAdmissible x y (fourierMukai x y K))
#check (AlgebraicGeometry.Scheme.QCoh.exactAdmissible_fourierMukai_of_mem x y :
  ∀ [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : exactFourierMukaiKernel x y),
    ExactAdmissible x y (fourierMukai x y K.obj))

end AlgebraicGeometry.Scheme.QCoh
