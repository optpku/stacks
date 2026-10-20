/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Dual
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.SelfExt
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Comparison

/-!
# Derived Evaluation for Dual Differential Graded Bimodules

This file promotes the explicit evaluation comparison
`N tensor_B T.dual ⟶ Hom_B(T, N)` through the canonical derived localizations.  Compactness of
`T` and computation of `RHom(T, -)` on the regular `B`-module make the resulting natural
transformation invertible.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.Dual

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

/-- On the homotopy category, the derived evaluation comparison is the derived-tensor counit,
followed by explicit evaluation, followed by the right-derived internal-Hom unit. -/
noncomputable def comparisonOnHomotopy
    (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    DifferentialGradedModule.Derived.Q B ⋙ Tensor.derivedFunctor T.dual ⟶
      DifferentialGradedModule.Derived.Q B ⋙ InternalHom.derivedFunctor T :=
  Tensor.derivedCounit T.dual ≫
    Functor.whiskerRight (comparisonK T) (DifferentialGradedModule.Derived.Q A) ≫
      InternalHom.derivedUnit T

/-- The canonical natural transformation
`- tensor_B^L T.dual ⟶ RHom_B(T, -)` on derived categories. -/
@[stacks 0BZ0 "derived tensor-dual to derived internal-Hom comparison"]
noncomputable def derivedComparison
    (T : DifferentialGradedBimodule.{u, v, v, v} A B) :
    Tensor.derivedFunctor T.dual ⟶ InternalHom.derivedFunctor T :=
  Localization.liftNatTrans
    (DifferentialGradedModule.Derived.Q B)
    (DifferentialGradedModule.quasiIso B)
    (DifferentialGradedModule.Derived.Q B ⋙ Tensor.derivedFunctor T.dual)
    (DifferentialGradedModule.Derived.Q B ⋙ InternalHom.derivedFunctor T)
    (Tensor.derivedFunctor T.dual) (InternalHom.derivedFunctor T)
    (comparisonOnHomotopy T)

/-- Compactness and invertibility of the right-derived unit on the regular module imply that
the canonical derived evaluation comparison is invertible. -/
theorem derivedComparison_isIso_of_compact_of_isIso_unit
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_compact : IsCompactObject
      ((DifferentialGradedModule.Derived.Q B).obj T.rightHomotopyObject))
    (h_unit : IsIso ((InternalHom.derivedUnit T).app
      (CochainDGAlgebra.RegularModule.shiftK B 0))) :
    IsIso (derivedComparison T) := sorry

/-- If `T` is compact in `D(B)` and the regular `B`-module computes
`RHom_B(T, -)`, then the canonical functorial comparison
`- tensor_B^L Hom_B(T, B) ⟶ RHom_B(T, -)` is an isomorphism. -/
@[stacks 0BZ0]
theorem derivedComparison_isIso_of_compact
    (T : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_regular : Functor.RightDerived.ComputesAt
      (InternalHom.derivedSourceFunctor T)
      (DifferentialGradedModule.quasiIso B)
      (CochainDGAlgebra.RegularModule.shiftK B 0))
    (h_compact : IsCompactObject
      ((DifferentialGradedModule.Derived.Q B).obj T.rightHomotopyObject)) :
    IsIso (derivedComparison T) := sorry

end DifferentialGradedBimodule.Dual
