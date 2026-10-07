module

public import stacks_project.Chap98.Lemma_98_27_16_Versal
public import stacks_project.Chap98.Lemma_98_27_16_Openness
public import stacks_project.Chap98.Lemma_98_27_4_Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Openness of versality for the Artin contraction functor

In Situation 98.27.1 the contraction functor on locally Noetherian schemes
over `S` satisfies openness of versality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.ContractionSituation

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.16: In Situation 98.27.1 the functor `σ.functor` satisfies
openness of versality. -/
@[stacks 0GIA, instance]
instance instOpennessOfVersality (σ : ContractionSituation S) :
    OpennessOfVersality σ.functor := sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
