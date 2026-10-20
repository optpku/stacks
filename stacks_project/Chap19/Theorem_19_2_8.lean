module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Baer.Transfinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

variable (R : Type u) [Ring R]

/- Theorem 19.2.8 (1): when `Cardinal.mk (Ideal R) < α.cof`, the specific transfinite Baer
object `(Baer.transfiniteFunctor R α).obj N` is injective. -/
@[stacks 05NX "(1)"] #check
  fun (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) (N : ModuleCat.{u} R) ↦
    Baer.transfiniteFunctor_obj_injective R α hα N

/- Theorem 19.2.8 (2): the same transfinite Baer functor and its canonical natural
monomorphism provide functorial injective embeddings. -/
@[stacks 05NX "(2)"] #check
  fun (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) ↦
    Baer.functorialInjectives R α hα

end ModuleCat
