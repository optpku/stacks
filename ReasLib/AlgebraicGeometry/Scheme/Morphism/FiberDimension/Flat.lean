module

public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Flat

/-!
# Fibre dimension of flat morphisms

Fibre dimension is constant along suitable specializations for flat, locally finitely
presented morphisms of schemes. For flat morphisms of finite presentation, the target-indexed
fibre-dimension function is lower semicontinuous.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat, locally finitely presented morphism, fibre dimension is unchanged along a
specialization `x' ⤳ x` when `x` is generic in an irreducible component of its fibre. -/
theorem fiberDimensionAt_eq_of_specializes_of_isGenericPoint_fiber {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] {x' x : X}
    (hxx : Specializes x' x)
    (hx : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    f.fiberDimensionAt x' = f.fiberDimensionAt x := sorry

namespace FinitePresentation

/-- The target-indexed fibre-dimension function of a flat finite-presentation morphism of
schemes is lower semicontinuous. -/
theorem lowerSemicontinuous_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Scheme.Hom.FinitePresentation f] :
    LowerSemicontinuous f.fiberDimension := sorry

end FinitePresentation

end AlgebraicGeometry.Scheme.Hom
