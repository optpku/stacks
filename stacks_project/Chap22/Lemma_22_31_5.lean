/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable (T : DifferentialGradedBimodule A B)
variable (hT : DifferentialGradedModule.Homotopy.kProjective B
  ((DifferentialGradedModule.toK B).obj T.toRightModule))

/- Lemma 22.31.5 (0BYW): a K-projective source computes derived internal Hom by ordinary
fixed-source internal Hom, functorially in the target. -/
@[stacks 0BYW] #check
  (DifferentialGradedBimodule.InternalHom.derivedUnit_isIso_of_kProjective T hT :
    IsIso (DifferentialGradedBimodule.InternalHom.derivedUnit T))

/- Property P is the source-facing sufficient condition for K-projectivity. -/
#check @DifferentialGradedBimodule.InternalHom.derivedUnit_isIso_of_hasPropertyP
#check @DifferentialGradedModule.HasPropertyP.kProjective

/- The reusable localization layer separates denominator inversion from the chosen derived
model. -/
#check @DifferentialGradedBimodule.InternalHom.derivedUnit_isIso_of_inverts
#check @DifferentialGradedBimodule.InternalHom.derivedFunctorIsoLiftOfInverts
#check @DifferentialGradedBimodule.InternalHom.derivedFunctor_isIsomorphic_lift_of_inverts
#check @CategoryTheory.Functor.RightDerived.isIsomorphic_total_lift
