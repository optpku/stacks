/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Dual.Derived
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (T : DifferentialGradedBimodule A B)
variable (h_regular : CategoryTheory.Functor.RightDerived.ComputesAt
  (DifferentialGradedBimodule.InternalHom.derivedSourceFunctor T)
  (DifferentialGradedModule.quasiIso B)
  (CochainDGAlgebra.RegularModule.shiftK B 0))
variable (h_compact : IsCompactObject
  ((DifferentialGradedModule.Derived.Q B).obj T.rightHomotopyObject))

/- Lemma 22.33.9 (1) (0BZ0): `Hom_B(T, B)` has its canonical `(B, A)`-bimodule structure. -/
@[stacks 0BZ0] #check
  (DifferentialGradedBimodule.dual T :
    DifferentialGradedBimodule B A)

/- Its underlying right `A`-module is the canonical internal Hom `Hom_B(T, B)`. -/
#check DifferentialGradedBimodule.Dual.dual_toRightModule T

/- Lemma 22.33.9 (2) (0BZ0): if `T` is compact and the regular module `B` computes
`RHom_B(T, B)`, the canonical derived evaluation comparison from tensoring with `T.dual` to
`RHom_B(T, -)` is an isomorphism. -/
@[stacks 0BZ0] #check
  DifferentialGradedBimodule.Dual.derivedComparison_isIso_of_compact T
    h_regular h_compact

#check @DifferentialGradedBimodule.Dual.leftAction
#check @DifferentialGradedBimodule.Dual.evaluation
#check @DifferentialGradedBimodule.Dual.comparisonK
#check @DifferentialGradedBimodule.Dual.derivedComparison
