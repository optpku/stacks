/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Morita.Tensor
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat.DegreeZero
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.DegreeZero
import StacksCheckRecall

@[expose] public section

noncomputable section

universe uR uA uB

open CategoryTheory
open scoped ModuleCat.Algebra

variable {R : Type uR} [CommRing R]
variable {A : Type uA} [Ring A] [Algebra R A]
variable {B : Type uB} [Ring B] [Algebra R B]

/- Lemma 22.37.8 (1) (09SC): ordinary derived Morita equivalence is characterized by a perfect
weak generator with the prescribed shifted endomorphisms. -/
@[stacks 09SC] #check
  (DerivedCategory.Morita.nonempty_equivalence_iff_exists_tilting
      (R := R) (A := A) (B := B) :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat (Aᵐᵒᵖ)))
      (DerivedCategory (ModuleCat (Bᵐᵒᵖ)))) ↔
      ∃ P : DerivedCategory (ModuleCat (Bᵐᵒᵖ)),
        DerivedCategory.Morita.IsTiltingFor R A P)

#check @DerivedCategory.Morita.IsTiltingFor
#check @DerivedCategory.Morita.isTiltingFor_iff
#check @DerivedCategory.Morita.isTiltingFor_iff_isPerfect
#check @DerivedCategory.Morita.IsTiltingFor.isCompact
#check @DerivedCategory.Morita.IsTiltingFor.isPerfect
#check @DerivedCategory.Morita.IsTiltingFor.isWeakGenerator
#check @DerivedCategory.Morita.IsTiltingFor.isSelfOrthogonal
#check @DerivedCategory.Morita.IsTiltingFor.selfExt_eq_zero
#check @DerivedCategory.Morita.IsTiltingFor.nonempty_endEquiv

variable [Module.Flat R B]

/- Lemma 22.37.8 (2) (09SC): over an `R`-flat target algebra, ordinary derived Morita
equivalence is equivalent to realization by derived tensoring with a DG bimodule complex
between the degree-zero DGA models. -/
@[stacks 09SC] #check
  (DerivedCategory.Morita.nonempty_equivalence_iff_exists_tensor
      (R := R) (A := A) (B := B) :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat.{max uA uB} (Aᵐᵒᵖ)))
      (DerivedCategory (ModuleCat.{max uA uB} (Bᵐᵒᵖ)))) ↔
      ∃ N : DifferentialGradedBimodule.{uR, max uA uB, uA, uB}
          (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B),
        (DifferentialGradedBimodule.Tensor.ordinaryDerivedFunctor.{uR, uA, uB,
          max uA uB, max uA uB} N).IsEquivalence)

#check @DifferentialGradedBimodule.Tensor.ordinaryDerivedFunctor
#check @DifferentialGradedBimodule.Tensor.ordinaryDerivedFunctor_commShift
#check @DifferentialGradedBimodule.Tensor.ordinaryDerivedFunctor_isTriangulated
#check @DifferentialGradedModule.DegreeZero.equivalence
#check @DifferentialGradedModule.DegreeZero.triangulatedEquivalence
#check @DifferentialGradedBimodule.DegreeZero.ofBimodule
#check @DifferentialGradedBimodule.DegreeZero.ofBimoduleFunctor
#check @DifferentialGradedBimodule.DegreeZero.ofBimoduleZeroIso
#check @DifferentialGradedBimodule.DegreeZero.ofBimodule_smul_pure
#check @DerivedCategory.Morita.exists_tilting_iff_exists_tensor
#check @CochainDGAlgebra.ofAlgebra_isKFlat
#check @CochainDGAlgebra.DerivedMorita.nonempty_equivalence_iff_exists_tensor
