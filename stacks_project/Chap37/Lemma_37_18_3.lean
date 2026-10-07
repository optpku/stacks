module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FlatPointClosure
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.18.3 (1): a generic point of an irreducible component of a fiber of the
reduced closure of a relatively associated point remains relatively associated wherever the
module is flat over the base. -/
@[stacks 0GSI] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.mem_of_flatOverAt_of_genericPoint :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (y : X) (t s : S) (hy_associated : y ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)
      (hy_image : f y = t) (x : (AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiber s)
      (hgeneric : x ∈ genericPoints ((AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiber s))
      (hflat : AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ f
        (((AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiberι s ≫
          AlgebraicGeometry.Scheme.PointClosure.ι y) x)),
      ((AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiberι s ≫
          AlgebraicGeometry.Scheme.PointClosure.ι y) x ∈
        AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)

/- Lemma 37.18.3 (2): at such a flat generic point, the local dimension of the chosen
fiber of the reduced point closure equals the dimension of its fiber over the image point. -/
@[stacks 0GSI] #check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.pointClosureFiber_dimension_eq_of_flatOverAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      (y : X) (t s : S) (hy_associated : y ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ)
      (hy_image : f y = t) (x : (AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiber s)
      (hgeneric : x ∈ genericPoints ((AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiber s))
      (hflat : AlgebraicGeometry.Scheme.Modules.flatOverAt ℱ f
        (((AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiberι s ≫
          AlgebraicGeometry.Scheme.PointClosure.ι y) x)),
      topologicalKrullDimAt x =
        topologicalKrullDim ((AlgebraicGeometry.Scheme.PointClosure.ι y ≫ f).fiber t))

end AlgebraicGeometry.Scheme.Modules
