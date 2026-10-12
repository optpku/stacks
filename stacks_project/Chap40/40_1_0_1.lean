/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
import StacksCheckRecall

@[expose] public section

universe u v w vB

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {U quotientStack :
  StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J}
variable (atlas : U ⟶ quotientStack)

namespace StackOver.Groupoids.TwoFibreProduct

/- 40.1.0.1: for the quotient atlas `atlas : U ⟶ quotientStack`, write `R` for the
canonical two-fibre product `apex atlas atlas`. The square

```text
R  ───▶ U
│       │
▼       ▼
U  ───▶ quotientStack
```

with both maps `U ⟶ quotientStack` equal to `atlas` is `2`-cartesian. -/
@[stacks 04LC]
#check (CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone.isBilimit atlas atlas :
  (CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone atlas atlas).IsBilimit)

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
