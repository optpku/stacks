module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linearity of ordinary-module realization functors

The equivalences between ordinary modules and one-sided bimodule objects respect the canonical
pointwise preadditive and linear structures.  The category structures themselves are owned by the
generic `CategoryTheory.Bimod` API; this file only records linearity of the ModuleCat-specific
realization functors.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

noncomputable section

universe u

namespace Module.Bimodule

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

namespace RightModuleFunctor

/-- Realizing an ordinary right module as a categorical right module is additive. -/
@[stacks 09LN "additive ordinary right-module realization"]
instance functorAdditive :
    (rightModuleFunctor (R := R) (A := A)).Additive := sorry

/-- Realizing an ordinary right module as a categorical right module is `R`-linear. -/
@[stacks 09LN "linear ordinary right-module realization"]
instance functorLinear :
    Functor.Linear R (rightModuleFunctor (R := R) (A := A)) := sorry

namespace Inverse

/-- Extracting an ordinary right module from a categorical right module is additive. -/
@[stacks 09LN "additive ordinary right-module extraction"]
instance functorAdditive :
    (functor (R := R) (A := A)).Additive := sorry

/-- Extracting an ordinary right module from a categorical right module is `R`-linear. -/
@[stacks 09LN "linear ordinary right-module extraction"]
instance functorLinear :
    Functor.Linear R (functor (R := R) (A := A)) := sorry

end Inverse

end RightModuleFunctor

namespace LeftModuleFunctor

/-- Realizing an ordinary left module as a categorical left module is additive. -/
@[stacks 09LN "additive ordinary left-module realization"]
instance functorAdditive :
    (leftModuleFunctor (R := R) (A := A)).Additive := sorry

/-- Realizing an ordinary left module as a categorical left module is `R`-linear. -/
@[stacks 09LN "linear ordinary left-module realization"]
instance functorLinear :
    Functor.Linear R (leftModuleFunctor (R := R) (A := A)) := sorry

namespace Inverse

/-- Extracting an ordinary left module from a categorical left module is additive. -/
@[stacks 09LN "additive ordinary left-module extraction"]
instance functorAdditive :
    (functor (R := R) (A := A)).Additive := sorry

/-- Extracting an ordinary left module from a categorical left module is `R`-linear. -/
@[stacks 09LN "linear ordinary left-module extraction"]
instance functorLinear :
    Functor.Linear R (functor (R := R) (A := A)) := sorry

end Inverse

end LeftModuleFunctor

#synth (rightModuleFunctor (R := R) (A := A)).Additive
#synth Functor.Linear R (rightModuleFunctor (R := R) (A := A))
#synth (RightModuleFunctor.Inverse.functor (R := R) (A := A)).Additive
#synth Functor.Linear R (RightModuleFunctor.Inverse.functor (R := R) (A := A))
#synth (leftModuleFunctor (R := R) (A := A)).Additive
#synth Functor.Linear R (leftModuleFunctor (R := R) (A := A))
#synth (LeftModuleFunctor.Inverse.functor (R := R) (A := A)).Additive
#synth Functor.Linear R (LeftModuleFunctor.Inverse.functor (R := R) (A := A))

end Module.Bimodule

end
