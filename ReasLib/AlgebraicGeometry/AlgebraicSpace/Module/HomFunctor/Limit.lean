module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Preservation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Limit preservation of the Hom functor

For a quasi-compact quasi-separated morphism of algebraic spaces, the Hom functor
from a finitely presented quasi-coherent module to a quasi-coherent module
preserves directed inverse limits of affine schemes over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a quasi-compact quasi-separated morphism `f`, finite presentation of the
quasi-coherent module `F` implies that `homFunctor f F G` preserves directed
inverse limits of affine schemes over `B`, for any quasi-coherent module `G`. -/
theorem homFunctor_preservesDirectedAffineLimits
    {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [QuasiCompact f] [QuasiSeparated f] (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFinitePresentation] :
    SchemeOver.PreservesDirectedAffineLimits B (homFunctor f F G) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
