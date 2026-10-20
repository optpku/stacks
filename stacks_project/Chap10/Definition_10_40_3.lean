module

public import Mathlib.Algebra.Module.Torsion.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.40.3

@stack 07T7
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/- Definition 10.40.3: given `m : M`, the annihilator of `m` is the canonical ideal
`Ideal.torsionOf R M m = {r : R | r • m = 0}`. -/
@[stacks 07T7 "annihilator of an element"]
#check @Ideal.torsionOf

/- Companion recall: membership in the annihilator of an element is exactly the textbook condition
`r • m = 0`. -/
@[stacks 07T7 "element annihilator membership"]
#check @Ideal.mem_torsionOf_iff

/- Companion recall: `Module.annihilator R M` is the canonical annihilator ideal of the module
`M`. -/
@[stacks 07T7 "annihilator of a module"]
#check @Module.annihilator

/- Companion recall: this is the standard membership characterization of the annihilator of a
module. -/
@[stacks 07T7 "module annihilator membership"]
#check @Module.mem_annihilator

end
