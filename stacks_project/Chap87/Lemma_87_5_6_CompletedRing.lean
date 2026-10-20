/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing

/-!
# Completed tensor product of linearly topologized algebras

The canonical map from the algebraic tensor product and the factor inclusions take values in the
compatible-family completion of the quotient-ring tensors.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra.TensorProduct

variable (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [TopologicalSpace A] [TopologicalSpace B]

#check (Completed.of R A B : A ⊗[R] B →+* Completed R A B)
#check (Completed.includeLeft R A B : A →+* Completed R A B)
#check (Completed.includeRight R A B : B →+* Completed R A B)

end Algebra.TensorProduct
