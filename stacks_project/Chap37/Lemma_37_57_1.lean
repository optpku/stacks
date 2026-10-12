/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.SeparatedLocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace FiniteType

/- Lemma 37.57.1: scheme descent data whose component structure morphisms are separated,
locally of finite type, and locally quasi-finite are effective for fppf coverings. -/
@[stacks 02W8] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.separatedLocallyQuasiFinite_satisfiesDescentFppf :
    MorphismProperty.SatisfiesDescent
      ((@IsSeparated ⊓ @LocallyOfFiniteType ⊓ @LocallyQuasiFinite) :
        MorphismProperty Scheme.{u}) .fppf)

end FiniteType
end Hom
end Scheme
end AlgebraicGeometry
