module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine

/-!
# Quasi-coherent relative differentials

The relative differential sheaf of a morphism of schemes is quasi-coherent.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The relative differential sheaf of a morphism of schemes is quasi-coherent. -/
instance isQuasicoherent_differentials (f : X ⟶ S) :
    (Ω[f.toShHom]).IsQuasicoherent := sorry

end AlgebraicGeometry
