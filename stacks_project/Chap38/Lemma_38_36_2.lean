module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme
namespace Ph
namespace Sheaf

/- Lemma 38.36.2: a sheaf on the big ph site over `S` sends a thickening
`f : X ⟶ X'` in `Over S` contravariantly to a bijection of section types. -/
@[stacks 0EW2] #check
  (AlgebraicGeometry.Scheme.Ph.Sheaf.map_bijective_of_isThickening :
    ∀ {S : Scheme.{u}}
      (𝓕 : CategoryTheory.Sheaf (Scheme.bigPhSite S) (Type v))
      {X X' : Over S} (f : X ⟶ X') [IsThickening f.left],
      Function.Bijective (𝓕.obj.map f.op))

end Sheaf
end Ph
end AlgebraicGeometry.Scheme
