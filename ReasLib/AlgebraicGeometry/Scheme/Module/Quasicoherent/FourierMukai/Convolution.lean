module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.UniversalVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ExactAdmissible

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

/-- The projection from the triple fiber product to its middle factor factors
through the projection to the first two factors. -/
theorem pr12_comp_snd :
    pr12 y z x ≫ Limits.pullback.snd x y =
      Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫
        Limits.pullback.snd x y := rfl

/-- The projection from the triple fiber product to its middle factor factors
through the projection to the last two factors. -/
theorem pr23_comp_fst :
    pr23 y z x ≫ Limits.pullback.fst y z =
      Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫
        Limits.pullback.snd x y := sorry

/-- The projection from the triple fiber product to its first factor factors
through the projection to the first and third factors. -/
theorem pr13_comp_fst :
    pr13 y z x ≫ Limits.pullback.fst x z =
      Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫
        Limits.pullback.fst x y := sorry

/-- The projection to the first and third factors is quasi-compact when
the first two schemes are quasi-compact with affine diagonal. -/
instance quasiCompact_pr13
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] :
    QuasiCompact (pr13 y z x) := sorry

/-- The projection to the first and third factors is quasi-separated when
the first two schemes are quasi-compact with affine diagonal. -/
instance quasiSeparated_pr13
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] :
    QuasiSeparated (pr13 y z x) := sorry

/-- The convolution of kernels on `X ×_R Y` and `Y ×_R Z` is the pushforward
of the tensor product of their pullbacks to `X ×_R Y ×_R Z`. -/
noncomputable def composeKernel
    [QuasiCompact (pr13 y z x)] [QuasiSeparated (pr13 y z x)]
    (K : Scheme.QCoh (Limits.pullback x y))
    (L : Scheme.QCoh (Limits.pullback y z)) :
    Scheme.QCoh (Limits.pullback x z) :=
  (Scheme.QCoh.pushforward (pr13 y z x)).obj
    ((tensorRight ((Scheme.QCoh.pullback (pr23 y z x)).obj L)).obj
      ((Scheme.QCoh.pullback (pr12 y z x)).obj K))

/-- Kernel convolution is `pr₁₃,*(pr₁₂^* K ⊗ pr₂₃^* L)`. -/
theorem composeKernel_obj
    [QuasiCompact (pr13 y z x)] [QuasiSeparated (pr13 y z x)]
    (K : Scheme.QCoh (Limits.pullback x y))
    (L : Scheme.QCoh (Limits.pullback y z)) :
    composeKernel x y z K L =
      (Scheme.QCoh.pushforward (pr13 y z x)).obj
        ((tensorRight ((Scheme.QCoh.pullback (pr23 y z x)).obj L)).obj
          ((Scheme.QCoh.pullback (pr12 y z x)).obj K)) := rfl

/-- Over a commutative ring, composition of exact linear coproduct-preserving
functors from quasi-compact schemes with affine diagonal is represented by
the convolution of any kernels representing the two functors. -/
theorem fourierMukaiKernel_comp
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y)
    (G : Scheme.QCoh Y ⥤ Scheme.QCoh Z)
    [ExactAdmissible x y F] [ExactAdmissible y z G]
    (K : Scheme.QCoh (Limits.pullback x y))
    (L : Scheme.QCoh (Limits.pullback y z))
    (hK : Nonempty (F ≅ fourierMukai x y K))
    (hL : Nonempty (G ≅ fourierMukai y z L)) :
    Nonempty (F ⋙ G ≅ fourierMukai x z (composeKernel x y z K L)) := sorry

end AlgebraicGeometry.Scheme.QCoh
