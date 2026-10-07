module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u v

namespace CochainDGAlgebra.RegularModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (M : DifferentialGradedModule.{u, v} A) (k : ℤ)

/- Lemma 22.16.2 (1) (09K1): closed morphisms from the shifted regular module `A[k]` to
`M` are canonically and `R`-linearly the cycles of `M` in degree `-k`. -/
@[stacks 09K1] #check
  (homLinearEquivCycles A M k :
    (shiftComp A k ⟶ (⟨M⟩ : Comp R (DifferentialGradedModule.{u, v} A))) ≃ₗ[R]
      M.cycles (-k))

/- Lemma 22.16.2 (2) (09K1): homotopy classes from the shifted regular module `A[k]` to
`M` are canonically and `R`-linearly the homology classes of `M` in degree `-k`. -/
@[stacks 09K1] #check
  (homotopyLinearEquivHomology A M k :
    (shiftK A k ⟶ (⟨M⟩ : K R (DifferentialGradedModule.{u, v} A))) ≃ₗ[R]
      M.homology (-k))

/- The forward maps are evaluation on the shifted unit, and are natural in `M`. -/
#check @cycleEvaluation
#check @cycleEvaluation_naturality
#check @homologyEvaluation
#check @homologyEvaluation_naturality

/- The underlying set equivalences remain available as compatibility companions. -/
#check @homEquivCycles
#check @homotopyEquivHomology

/- The underlying-complex construction is exposed functorially and faithfully. -/
#check @DifferentialGradedModule.forgetToComplex
#synth Functor.Faithful (DifferentialGradedModule.forgetToComplex.{u, v} A)
#synth (DifferentialGradedModule.forgetToComplex.{u, v} A).Additive
#synth Functor.Linear R (DifferentialGradedModule.forgetToComplex.{u, v} A)

/- Degreewise homology is obtained by composing the forgetful functor with mathlib homology. -/
#check @DifferentialGradedModule.homologyFunctor

end CochainDGAlgebra.RegularModule
