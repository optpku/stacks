module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Ampleness of external tensor products

This file records ampleness of the external tensor product of ample invertible
modules over a quasi-separated base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The external tensor product of ample invertible modules over a quasi-separated scheme is
ample on the fiber product. -/
theorem isAmple_externalTensorProduct
    {S X Y : Scheme.{u}} [QuasiSeparatedSpace S]
    (f : X ⟶ S) (g : Y ⟶ S) (L : X.Modules) (N : Y.Modules)
    [Invertible L] [Invertible N] [IsAmple L] [IsAmple N] :
    IsAmple (externalTensorProduct f g L N) := sorry

/-- External tensor products canonically preserve ampleness over a quasi-separated scheme. -/
instance instIsAmple_externalTensorProduct
    {S X Y : Scheme.{u}} [QuasiSeparatedSpace S]
    (f : X ⟶ S) (g : Y ⟶ S) (L : X.Modules) (N : Y.Modules)
    [Invertible L] [Invertible N] [IsAmple L] [IsAmple N] :
    IsAmple (externalTensorProduct f g L N) :=
  isAmple_externalTensorProduct f g L N

end AlgebraicGeometry.Scheme.Modules
