/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Unit
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Regular Object under Derived Tensor

The underived tensor-unit isomorphism and the derived-tensor comparison identify the image of
the regular object with the object represented by the fixed differential graded bimodule.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open scoped DifferentialGradedModule

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The derived-tensor counit is invertible on the unshifted regular module. -/
@[stacks 09R9 "the regular module computes derived tensor"]
instance derivedCounit_regular_isIso (N : DifferentialGradedBimodule.{u, w, w, x} A B) :
    IsIso ((derivedCounit.{u, w, w, w, x} N).app
      ((DifferentialGradedModule.toK A).obj A.regularModule)) := sorry

/-- Derived tensoring sends the regular object of `D(A)` to the object of `D(B)` represented by
the underlying right module of `N`. -/
@[stacks 09R9 "derived tensor image of the regular object"]
noncomputable def regularObjectIso
    (N : DifferentialGradedBimodule.{u, w, w, x} A B) :
    (derivedFunctor.{u, w, w, w, x} N).obj
        (DifferentialGradedModule.Derived.regularObject A) ≅
      N.rightDerivedObject :=
  ((derivedFunctor.{u, w, w, w, x} N).mapIso
      ((DifferentialGradedModule.Derived.Q A).mapIso
        (DifferentialGradedModule.Derived.regularZeroIso A))).trans
    ((asIso ((derivedCounit.{u, w, w, w, x} N).app
        ((DifferentialGradedModule.toK A).obj A.regularModule))).trans
      ((DifferentialGradedModule.Derived.Q B).mapIso
        ((DifferentialGradedModule.toK B).mapIso
          (regularTensorIso (R := R) (A := A) (B := B) N))))

end DifferentialGradedBimodule.Tensor
