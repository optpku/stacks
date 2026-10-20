module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Conditions
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- A morphism between locally Noetherian schemes is locally of finite
presentation if its functor of points, restricted to locally Noetherian
schemes over the base, preserves directed affine limits. -/
@[stacks 0GE4]
theorem locallyFinitePresentation_of_noetherianDirectedAffineLimits
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian X]
    (f : X ⟶ S)
    (hF : Extension.PreservesDirectedAffineLimits (locallyNoetherian S)
      ((locallyNoetherian S).ι.op ⋙ yoneda.obj (Over.mk f))) :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.Scheme.Over
