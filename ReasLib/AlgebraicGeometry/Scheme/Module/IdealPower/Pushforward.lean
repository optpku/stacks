module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Product
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

/-!
# Ideal products and pushforwards

This file records the compatibility of multiplication by an ideal sheaf with pushforward along
an affine morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- For an affine morphism, multiplying a pushed-forward quasi-coherent module by an ideal sheaf
agrees with the image under pushforward of multiplication by the pulled-back ideal sheaf. -/
theorem idealPowerProductSubobject_pushforward_eq_map_of_isAffineHom
    (f : Y ⟶ X) [IsAffineHom f]
    (ℱ : Y.Modules) [ℱ.IsQuasicoherent] (I : X.IdealSheafData) :
    idealPowerProductSubobject I ((pushforward f).obj ℱ) 1 =
      (Subobject.map
          ((pushforward f).map (idealPowerProductSubobject (I.comap f) ℱ 1).arrow)).obj ⊤ := sorry

end AlgebraicGeometry.Scheme.Modules
