module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {S : ShortComplex (DifferentialGradedModule.{u, w} A)}
variable (hS : IsAdmissibleShortExact S) (sigma : ShortComplex.GradedSplitting S)
variable (i j : ℤ) (hij : i + 1 = j)

/- Lemma 22.7.2 (09JU): the connecting morphism defined by a graded `A`-linear splitting
induces the canonical boundary map of the underlying short exact sequence. -/
@[stacks 09JU] #check
  (ShortComplex.boundary_eq_connecting hS sigma i j hij :
    CochainComplex.homologyδOfTriangle
        (CochainComplex.triangleOfDegreewiseSplit
          (S.map (forgetToComplex A)) sigma.toDegreewiseSplitting) i j hij =
      (ShortComplex.admissibleShortExact_map_forgetToComplex hS).δ i j hij)

/- The construction-facing owner is a DG-module morphism whose coordinates are section,
differential, then retraction. -/
#check (sigma.connectingHom : S.X₃ ⟶ S.X₁[1])
