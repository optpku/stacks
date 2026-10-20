module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.Topology.KrullDimension.Local

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- A generic point of a fiber component of the reduced closure of a relatively associated
point remains relatively associated wherever the module is flat over the base. -/
theorem mem_of_flatOverAt_of_genericPoint {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : X) (t s : S) (hy_associated : y ∈ relativeAssassin f ℱ)
    (hy_image : f y = t) (x : (PointClosure.ι y ≫ f).fiber s)
    (hgeneric : x ∈ genericPoints ((PointClosure.ι y ≫ f).fiber s))
    (hflat : flatOverAt ℱ f (((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x)) :
    ((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x ∈ relativeAssassin f ℱ := sorry

/-- At a flat generic point of a fiber of a reduced point closure, the local dimension equals
the dimension of the fiber over the image of the original point. -/
theorem pointClosureFiber_dimension_eq_of_flatOverAt {X S : Scheme.{u}}
    (f : X ⟶ S) (ℱ : X.Modules)
    [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : X) (t s : S) (hy_associated : y ∈ relativeAssassin f ℱ)
    (hy_image : f y = t) (x : (PointClosure.ι y ≫ f).fiber s)
    (hgeneric : x ∈ genericPoints ((PointClosure.ι y ≫ f).fiber s))
    (hflat : flatOverAt ℱ f (((PointClosure.ι y ≫ f).fiberι s ≫ PointClosure.ι y) x)) :
    topologicalKrullDimAt x = topologicalKrullDim ((PointClosure.ι y ≫ f).fiber t) := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
