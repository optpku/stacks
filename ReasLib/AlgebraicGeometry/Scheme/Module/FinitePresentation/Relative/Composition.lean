module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
import ReasLib.Algebra.Module.FinitePresentation.Relative.BaseChange

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules
namespace IsFinitePresentationOver

/-- Relative finite presentation of a quasicoherent scheme module ascends along a locally
finitely presented morphism of base schemes. -/
theorem comp {X Y S : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f]
    {F : X.Modules} [F.IsQuasicoherent] (hF : F.IsFinitePresentationOver f)
    (g : Y ⟶ S) [LocallyOfFinitePresentation g] :
    F.IsFinitePresentationOver (f ≫ g) := sorry

end IsFinitePresentationOver
end Scheme.Modules
end AlgebraicGeometry
