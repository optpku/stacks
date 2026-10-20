module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Baer.Step
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace ModuleCat

variable (R : Type u) [Ring R]

/- 19.2.6.1: `Baer.step R M` is the pushout of the coproduct of all maps from ideals into `M`
along the coproduct of the corresponding ideal inclusions into copies of `R`. -/
@[stacks 05NV] #check
  fun M : ModuleCat.{u} R ↦
    (Baer.square R M :
      CommSq (Baer.toRing R M) (Baer.toModule R M)
        (Baer.fromRing R M) (Baer.inclusion R M))

end ModuleCat
