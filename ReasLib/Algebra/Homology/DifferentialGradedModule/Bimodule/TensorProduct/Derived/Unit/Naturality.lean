/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Unit

/-!
# Naturality of the regular-object derived tensor isomorphism

The identification of derived tensoring the regular module with the underlying right derived
object is natural in the differential graded bimodule parameter.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The regular-object derived tensor isomorphism is natural in the bimodule. -/
@[reassoc, stacks 09R9 "naturality of the regular-object derived tensor isomorphism"]
theorem regularObjectIso_naturality
    {N N' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : N ⟶ N') :
    (derivedNatTrans.{u, w, w, w, x} f).app
        (DifferentialGradedModule.Derived.regularObject A) ≫
        (regularObjectIso N').hom =
      (regularObjectIso N).hom ≫
        (DifferentialGradedBimodule.rightDerivedObjectFunctor A B).map f := sorry

/-- The inverse regular-object comparison satisfies the equivalent naturality square. -/
@[reassoc, stacks 09R9 "inverse regular-object comparison naturality"]
theorem regularObjectIso_inv_naturality
    {N N' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : N ⟶ N') :
    (DifferentialGradedBimodule.rightDerivedObjectFunctor A B).map f ≫
        (regularObjectIso N').inv =
      (regularObjectIso N).inv ≫
        (derivedNatTrans f).app
          (DifferentialGradedModule.Derived.regularObject A) := sorry

end DifferentialGradedBimodule.Tensor
