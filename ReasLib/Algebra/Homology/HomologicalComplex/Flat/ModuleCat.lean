module

public import ReasLib.Algebra.Category.ModuleCat.Flat
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise-flat complexes of modules

@stack 064K

The canonical termwise-flat predicate for a homological complex is categorical.  This file gives
its degreewise algebraic characterization for complexes in `ModuleCat`, for an arbitrary complex
shape and indexing type.
-/

@[expose] public section

universe u w

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable {ι : Type w} {c : ComplexShape ι}

/-- A complex of bundled modules is categorically termwise flat exactly when every underlying
module is algebraically flat. -/
@[stacks 064K "termwise-flat bridge"]
theorem isTermwiseFlat_iff_module_flat
    (K : HomologicalComplex (ModuleCat.{u} R) c) :
    IsTermwiseFlat K ↔ ∀ i : ι, Module.Flat R (K.X i) := sorry

namespace IsTermwiseFlat

/-- Every component of a categorically termwise-flat complex of modules is algebraically flat. -/
@[stacks 064K "categorical-to-algebraic bridge"]
theorem moduleFlat {K : HomologicalComplex (ModuleCat.{u} R) c}
    (hK : IsTermwiseFlat K) (i : ι) : Module.Flat R (K.X i) := sorry

end IsTermwiseFlat

/-- Algebraic flatness in every degree constructs categorical termwise flatness for a complex of
modules. -/
@[stacks 064K "algebraic-to-categorical bridge"]
theorem isTermwiseFlat_of_forall_moduleFlat
    (K : HomologicalComplex (ModuleCat.{u} R) c)
    (hK : ∀ i : ι, Module.Flat R (K.X i)) : IsTermwiseFlat K := sorry



end HomologicalComplex
