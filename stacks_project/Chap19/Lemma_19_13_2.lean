module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/- Lemma 19.13.2: a Grothendieck abelian category has `AB3*`, i.e. it has products; this is
the canonical structure `HasProducts A`, justified upstream by the stronger instance
`IsGrothendieckAbelian.hasLimits`. -/
@[stacks 07D8] #check (inferInstance : HasProducts A)

end CategoryTheory
