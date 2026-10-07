module

public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Proper

/-!
# Fibre dimension of proper flat morphisms

The target-indexed dimension of the fibres of a proper flat morphism of finite presentation
is locally constant.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- The target-indexed fibre-dimension function of a proper flat finite-presentation morphism
of schemes is locally constant. -/
theorem isLocallyConstant_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f] :
    IsLocallyConstant f.fiberDimension := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
