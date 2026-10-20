module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace FiniteType

/-- Scheme descent data whose component structure morphisms are separated, locally of finite
type, and locally quasi-finite are effective for fppf coverings. -/
theorem separatedLocallyQuasiFinite_satisfiesDescentFppf :
    MorphismProperty.SatisfiesDescent
      ((@IsSeparated ⊓ @LocallyOfFiniteType ⊓ @LocallyQuasiFinite) :
        MorphismProperty Scheme.{u}) .fppf := sorry

end FiniteType
end Hom
end Scheme
end AlgebraicGeometry
