module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Quasi-coherent relative differentials

The relative differential sheaf of a morphism of algebraic spaces is
quasi-coherent.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The sheaf of relative differentials of a morphism of algebraic spaces over a scheme
is a quasi-coherent module. -/
instance isQuasicoherent_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (Ω[f]).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
