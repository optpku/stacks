module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Colimit.Sequential
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (S : ℕ ⥤ DifferentialGradedModule.{u, v} A)

/- Lemma 22.23.2 (0CRL): for a sequential diagram of right differential graded modules over a DG
algebra, the derived image of its termwise colimit is a homotopy colimit. -/
@[stacks 0CRL]
#check
  (DifferentialGradedModule.Derived.SequentialColimit.isOf S :
    HomotopyColimit.IsOf
      (S ⋙ DifferentialGradedModule.Derived.fromModules A)
      ((DifferentialGradedModule.Derived.fromModules A).obj (colimit S)))

/- The reusable owner exposes the canonical telescope presentation and its distinguished
triangle. -/
#check CategoryTheory.DeltaFunctor.SequentialColimit.presentation
  (DifferentialGradedModule.Derived.Delta.functor A) S
#check CategoryTheory.DeltaFunctor.SequentialColimit.distinguished
  (DifferentialGradedModule.Derived.Delta.functor A) S
