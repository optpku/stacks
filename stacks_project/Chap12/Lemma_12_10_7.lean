module

public import ReasLib.CategoryTheory.Abelian.SerreQuotient
import StacksCheckRecall

@[expose] public section

universe uA vA uB vB

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (P : ObjectProperty A) [P.IsSerreClass]
variable (G : A ⥤ₑ B) (hPker : P ≤ G.obj.kernel)

/- Lemma 12.10.7 [06XK]: the prescribed Serre class is the kernel exactly when the induced
functor on the Serre quotient is faithful. -/
@[stacks 06XK]
#check (kernel_eq_iff_inducedFunctor_faithful P G hPker :
  P = G.obj.kernel ↔ (inducedFunctor P G hPker).Faithful)

/- The induced functor is also exposed as a bundled exact functor for downstream composition. -/
#check (inducedExactFunctor P G hPker : P.isoModSerre.Localization ⥤ₑ B)

end CategoryTheory.ObjectProperty.SerreClassLocalization
