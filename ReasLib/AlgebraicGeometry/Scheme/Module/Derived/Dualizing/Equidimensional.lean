module

public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace NormalizedDualizingComplex
namespace RelativeTo

/-- For an equidimensional finite-type scheme over a field, the cohomology sheaf in the
dimension degree of a relative normalized dualizing complex is a dualizing module. -/
theorem isDualizingModule_of_equidimensional
    {k : Type u} [Field k] (X : Scheme.FiniteTypeOver (Spec (CommRingCat.of k)))
    [TopologicalSpace.EquidimensionalSpace X.obj.left]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace))
    (HX : MonoidalClosed (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace))
    (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (hωS_affine : IsIsomorphic ωS
      ((affineTildeDerived k).obj (ModuleCat.single0 (ModuleCat.of k k))))
    (ωX : RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)
    (hωX : @RelativeTo _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX)
    (d : ℕ) (h_dimension : topologicalKrullDim X.obj.left = d) :
    RingedSpace.ModuleDerived.IsDualizingModule ωX HX (-(d : ℤ))
      (RingedSpace.ModuleDerived.cohomologySheaf ωX (-(d : ℤ))) := sorry

end RelativeTo
end NormalizedDualizingComplex
end Hom
end Scheme
end AlgebraicGeometry
