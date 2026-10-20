/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Henselization
import StacksCheckRecall

open AlgebraicGeometry
open scoped TensorProduct TensorProduct.Right

universe u v w

@[expose] public section

/- Lemma 38.2.9: weak association of a quasi-coherent module at a scheme point is
equivalent to weak association of the stalk maximal ideal before scalar extension,
after henselization, and after strict henselization. -/
@[stacks 0CTU] #check
  (AlgebraicGeometry.Scheme.Modules.mem_weakAss_henselization_tfae :
    ∀ {S : Scheme.{u}} (s : S) (F : S.Modules) [F.IsQuasicoherent]
      (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
      [IsHenselizationOf (S.presheaf.stalk s) Rh]
      (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh]
      [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh],
      List.TFAE [
        s ∈ F.weakAss,
        Ideal.IsWeaklyAssociatedToModule (S.presheaf.stalk s)
          (RingedSpace.stalkModuleCat F s)
          (IsLocalRing.maximalIdeal (S.presheaf.stalk s)),
        Ideal.IsWeaklyAssociatedToModule Rh
          ((RingedSpace.stalkModuleCat F s) ⊗[S.presheaf.stalk s] Rh)
          (IsLocalRing.maximalIdeal Rh),
        Ideal.IsWeaklyAssociatedToModule Rsh
          ((RingedSpace.stalkModuleCat F s) ⊗[S.presheaf.stalk s] Rsh)
          (IsLocalRing.maximalIdeal Rsh)])
