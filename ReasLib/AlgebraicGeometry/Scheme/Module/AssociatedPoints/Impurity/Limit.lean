module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace Impurity

/-- An impurity over a directed inverse limit of affine schemes over the base descends,
through a canonical cone projection, to an impurity at some finite stage. -/
theorem exists_stage {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (J : Impurity F f s)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S)
    (π : (Functor.const (OrderDual I)).obj (Over.mk J.g) ⟶ D)
    (hπ : IsLimit (⟨Over.mk J.g, π⟩ : Cone D))
    [∀ i : I, IsAffine (D.obj i).left] :
    ∃ i : I, J.DescendsAlong (D.obj i).hom (π.app i).left (π.app i).w := sorry

end Impurity
end Modules
end Scheme
end AlgebraicGeometry
