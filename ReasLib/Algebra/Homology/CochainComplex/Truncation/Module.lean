module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module properties of good lower truncations

At the cutoff degree the good lower truncation has the incoming opcycles as its term; above the
cutoff it is degreewise isomorphic to the original complex, and below it is zero.  The statements
here expose the resulting reusable termwise flatness and finite-presentation interfaces.  Relative
flatness is stated with the canonical `Module.FlatAlong` predicate; the explicit restricted-module
form remains available through the termwise bridge API.
@stack 0E1U
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
variable {σ : R →+* A}
variable {K : CochainComplex (ModuleCat A) ℤ}

namespace IsTermwiseFlatAlong

/-- Stacks `0E1U`: good lower truncation preserves relative termwise flatness when its cutoff opcycles are flat. -/
@[stacks 0E1U "relative flatness of a good lower truncation"]
theorem truncGE_of_opcycles
    (hK : K.IsTermwiseFlatAlong σ) (a : ℤ)
    (hop : Module.FlatAlong σ (K.opcycles a)) :
    (K.truncGE a).IsTermwiseFlatAlong σ := sorry

end IsTermwiseFlatAlong

namespace IsTermwiseFlatOver

variable [Algebra R A]

/-- Stacks `0E1U`: algebra-map specialization of relative flatness for a good lower truncation. -/
@[stacks 0E1U "relative flatness of an algebra-map truncation"]
theorem truncGE_of_opcycles
    (hK : K.IsTermwiseFlatOver R) (a : ℤ)
    (hop : Module.FlatAlong (algebraMap R A) (K.opcycles a)) :
    (K.truncGE a).IsTermwiseFlatOver R := sorry

end IsTermwiseFlatOver

namespace IsTermwiseFinitePresentation

/-- Stacks `0E1U`: good lower truncation preserves termwise finite presentation when its cutoff opcycles are
finitely presented. -/
@[stacks 0E1U "finite presentation of a good lower truncation"]
theorem truncGE_of_opcycles
    (hK : K.IsTermwiseFinitePresentation) (a : ℤ)
    (hop : Module.FinitePresentation A (K.opcycles a)) :
    (K.truncGE a).IsTermwiseFinitePresentation := sorry

end IsTermwiseFinitePresentation

end CochainComplex

end
