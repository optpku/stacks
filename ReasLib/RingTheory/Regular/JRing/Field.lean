/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fields are J-rings

@stack 07PJ
-/

@[expose] public section

universe u v

namespace IsJ0Ring

/-- Every field is `J-0`. -/
@[stacks 07PJ "(1), fields are J-0"]
instance field (K : Type u) [Field K] : IsJ0Ring K := sorry

end IsJ0Ring

namespace IsJ1Ring

/-- Every field is `J-1`. -/
@[stacks 07PJ "(1), fields are J-1"]
instance field (K : Type u) [Field K] : IsJ1Ring K := sorry

end IsJ1Ring

namespace IsJ2Ring

/-- Every field is `J-2`. -/
@[stacks 07PJ "(1), fields"]
instance field (K : Type u) [Field K] : IsJ2Ring.{u, v} K := sorry

end IsJ2Ring
