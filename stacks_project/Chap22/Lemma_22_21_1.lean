module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Milnor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {I : DifferentialGradedModule.{u, v} A}
variable (F : DifferentialGradedModule.PropertyI.Filtration A I)

/- Lemma 22.21.1 (09KR): a property `(I)` filtration gives the short exact Milnor product
sequence `0 ⟶ I ⟶ ∏ i, I / F_i I ⟶ ∏ i, I / F_i I ⟶ 0`. -/
@[stacks 09KR] #check
  (DifferentialGradedModule.PropertyI.Filtration.milnorIsAdmissibleShortExact F :
    DifferentialGradedModule.IsAdmissibleShortExact F.milnorShortComplex)
