module

public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
public import ReasLib.RingTheory.Coherent.Operations

@[expose] public section

/-!
# Coherence and Short Exact Sequences

The three-out-of-three closure API for coherent modules in a short exact sequence.
-/

universe u v

open CategoryTheory

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- In a short exact sequence of `R`-modules, coherent endpoints imply a coherent middle term. -/
theorem coherent_X2_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₁]
    [Module.Coherent R S.X₃] :
    Module.Coherent R S.X₂ := sorry

/-- In a short exact sequence of `R`-modules, coherent middle and right terms imply a coherent
left term. -/
theorem coherent_X1_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₂]
    [Module.Coherent R S.X₃] :
    Module.Coherent R S.X₁ := sorry

/-- In a short exact sequence of `R`-modules, coherent left and middle terms imply a coherent
right term. -/
theorem coherent_X3_of_shortExact (hS : S.ShortExact) [Module.Coherent R S.X₁]
    [Module.Coherent R S.X₂] :
    Module.Coherent R S.X₃ := sorry

end

end CategoryTheory.ShortComplex
