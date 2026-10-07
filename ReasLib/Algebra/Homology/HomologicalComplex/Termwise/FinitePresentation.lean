module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise finite-presentation complexes

This leaf owns the shape-independent finite-presentation condition for complexes of modules.
The condition is explicit and degreewise, so it can be combined with support bounds without
installing noncanonical instances.
@stack 0E1U
-/

@[expose] public section

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R]
variable {ι : Type v} {c : ComplexShape ι}

/-- Stacks `058R`: a module-valued homological complex is termwise finitely presented when every component is a
finitely presented module. -/
@[stacks 0E1U "termwise finite-presentation complexes"]
def IsTermwiseFinitePresentation
    (K : HomologicalComplex (ModuleCat R) c) : Prop :=
  ∀ i : ι, Module.FinitePresentation R (K.X i)

namespace IsTermwiseFinitePresentation

variable {K : HomologicalComplex (ModuleCat R) c}

/-- Stacks `058R`: a specified component of a termwise finitely presented complex is finitely presented. -/
@[stacks 0E1U "finite-presentation components of termwise finite-presentation complexes"]
theorem finitePresentation
    (hK : K.IsTermwiseFinitePresentation) (i : ι) :
    Module.FinitePresentation R (K.X i) := sorry
/- Proof strategy: specialize the defining degreewise predicate at `i`. -/

end IsTermwiseFinitePresentation

/-- Stacks `058R`: termwise finite presentation unfolds degreewise. -/
@[stacks 0E1U "degreewise termwise finite-presentation criterion"]
theorem isTermwiseFinitePresentation_iff
    (K : HomologicalComplex (ModuleCat R) c) :
    K.IsTermwiseFinitePresentation ↔
      ∀ i : ι, Module.FinitePresentation R (K.X i) := sorry
/- Proof strategy: unfold `HomologicalComplex.IsTermwiseFinitePresentation` and use the identity
implications in the two directions. -/

end HomologicalComplex

namespace ChainComplex

variable {R : Type u} [Ring R]

/-- Stacks `058R`: the chain-complex specialization of termwise finite presentation. -/
@[stacks 0E1U "chain-complex termwise finite presentation"]
abbrev IsTermwiseFinitePresentation
    (K : ChainComplex (ModuleCat R) ℕ) : Prop :=
  HomologicalComplex.IsTermwiseFinitePresentation K

end ChainComplex

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- Stacks `058R`: the integer cochain-complex specialization of termwise finite presentation. -/
@[stacks 0E1U "cochain-complex termwise finite presentation"]
abbrev IsTermwiseFinitePresentation
    (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  HomologicalComplex.IsTermwiseFinitePresentation K

end CochainComplex
