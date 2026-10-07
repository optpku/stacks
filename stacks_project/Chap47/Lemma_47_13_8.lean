module

public import stacks_project.Chap47.Situation_47_13_6
public import stacks_project.Chap22.Lemma_22_33_9
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R]
variable {E : CochainDGAlgebra.{u, u} R}

/- Lemma 47.13.8: let `E` be as in Situation 47.13.6 and regard it as the
`(E, R)`-bimodule obtained by restricting its regular module along `R ⟶ E`. If this
underlying object is compact in `D(R)` and `Hom_R(E, R)` computes `RHom_R(E, R)`, then
the canonical comparison from `K ↦ K ⊗ᴸ_R Hom_R(E, R)` to `RHom_R(E, K)`, valued in
`D(E)`, is an isomorphism of functors. -/
@[stacks 0BZD] #check
  (DifferentialGradedBimodule.Dual.derivedComparison_isIso_of_compact
    (DifferentialGradedBimodule.ChangeOfRings.restriction
      (CochainDGAlgebra.Hom.fromBase E)) :
    (h_regular : Functor.RightDerived.ComputesAt
      (DifferentialGradedBimodule.InternalHom.derivedSourceFunctor
        (DifferentialGradedBimodule.ChangeOfRings.restriction
          (CochainDGAlgebra.Hom.fromBase E)))
      (DifferentialGradedModule.quasiIso (CochainDGAlgebra.ofAlgebra R R))
      (CochainDGAlgebra.RegularModule.shiftK (CochainDGAlgebra.ofAlgebra R R) 0))
      →
    (h_compact : IsCompactObject
      (DifferentialGradedBimodule.ChangeOfRings.restriction
        (CochainDGAlgebra.Hom.fromBase E)).rightDerivedObject)
      →
    IsIso (DifferentialGradedBimodule.Dual.derivedComparison
      (DifferentialGradedBimodule.ChangeOfRings.restriction
        (CochainDGAlgebra.Hom.fromBase E))))
