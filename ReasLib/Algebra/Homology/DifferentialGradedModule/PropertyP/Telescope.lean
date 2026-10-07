module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP

/-!
# The telescope sequence of a property P filtration
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.PropertyP.Filtration

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {P : DifferentialGradedModule.{u, v} A}

/-- The telescope short complex associated to a property P filtration. -/
abbrev telescopeShortComplex (F : Filtration A P) :
    ShortComplex (DifferentialGradedModule.{u, v} A) :=
  F.toSequentialColimitFiltration.telescopeShortComplex

/-- Lemma 22.20.1 (09KL): the telescope sequence associated to a property P filtration is
admissibly short exact. -/
@[stacks 09KL, stacks 0FQL]
theorem telescopeIsAdmissibleShortExact (F : Filtration A P) :
    DifferentialGradedModule.IsAdmissibleShortExact F.telescopeShortComplex := sorry

end DifferentialGradedModule.PropertyP.Filtration
