module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal

/-!
# Derived sheaf internal Hom on a ringed space

The module category of the opens ringed site is the native module category of the ringed
space. This specialization reuses the actual sheaf-valued bifunctor and its shift matrices;
it does not select a monoidal or closed structure on the derived category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Pretriangulated.Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.InternalHom

variable (X : RingedSpace.{u})

/-- The actual sheaf-valued derived internal-Hom bifunctor of the ringed space's modules. -/
def functor : (ModuleDerived X)ᵒᵖ × ModuleDerived X ⥤ ModuleDerived X :=
  RingedSite.Hom.ModuleDerived.InternalHom.functor
    (J := Opens.grothendieckTopology X) (O := X.sheaf)

/-- The source-first curried form of the actual sheaf-valued derived internal Hom. -/
def curried : (ModuleDerived X)ᵒᵖ ⥤ ModuleDerived X ⥤ ModuleDerived X :=
  Functor.curry.obj (functor X)

/-- The actual contravariant source-variable internal-Hom functor on the native derived category. -/
def sourceFunctor (N : ModuleDerived X) : (ModuleDerived X)ᵒᵖ ⥤ ModuleDerived X :=
  (curried X).flip.obj N

/-- The actual covariant target-variable internal-Hom functor on the native derived category. -/
def targetFunctor (M : ModuleDerived X) : ModuleDerived X ⥤ ModuleDerived X :=
  (curried X).obj (Opposite.op M)

/-- Source-variable shifts are the existing actual negative-source sheaf-Hom comparisons. -/
@[stacks 08I0 "actual sheaf-valued source-variable shift compatibility"]
instance sourceFunctor_commShift (N : ModuleDerived X) :
    (sourceFunctor X N).CommShift ℤ :=
  RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor_commShift
    (J := Opens.grothendieckTopology X) (O := X.sheaf) N

/-- Target-variable shifts are the existing actual covariant sheaf-Hom comparisons. -/
@[stacks 08I0 "actual sheaf-valued target-variable shift compatibility"]
instance targetFunctor_commShift (M : ModuleDerived X) :
    (targetFunctor X M).CommShift ℤ :=
  RingedSite.Hom.ModuleDerived.InternalHom.targetFunctor_commShift
    (J := Opens.grothendieckTopology X) (O := X.sheaf) M

/-- The actual derived sheaf internal Hom preserves distinguished triangles in its source. -/
@[stacks 08I0 "actual sheaf-valued source-variable triangulated functor"]
instance sourceFunctor_isTriangulated (N : ModuleDerived X) :
    (sourceFunctor X N).IsTriangulated :=
  RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor_isTriangulated
    (J := Opens.grothendieckTopology X) (O := X.sheaf) N

/-- The actual derived sheaf internal Hom preserves distinguished triangles in its target. -/
@[stacks 08I0 "actual sheaf-valued target-variable triangulated functor"]
instance targetFunctor_isTriangulated (M : ModuleDerived X) :
    (targetFunctor X M).IsTriangulated :=
  RingedSite.Hom.ModuleDerived.InternalHom.targetFunctor_isTriangulated
    (J := Opens.grothendieckTopology X) (O := X.sheaf) M

end AlgebraicGeometry.RingedSpace.ModuleDerived.InternalHom
