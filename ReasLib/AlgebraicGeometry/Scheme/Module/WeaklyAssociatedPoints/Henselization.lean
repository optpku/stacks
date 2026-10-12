/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points and henselization

Weak association of a quasi-coherent module at a scheme point is invariant
under extension of the stalk to a henselization or strict henselization.
-/

@[expose] public section

open AlgebraicGeometry
open scoped TensorProduct TensorProduct.Right

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

/-- A point is weakly associated to a quasi-coherent module if and only if the maximal ideal
of a henselization is weakly associated to the scalar-extended stalk. -/
theorem mem_weakAss_iff_henselization
    {S : Scheme.{u}} (s : S) (F : S.Modules) [F.IsQuasicoherent]
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh] :
    s ∈ F.weakAss ↔
      Ideal.IsWeaklyAssociatedToModule Rh
        ((RingedSpace.stalkModuleCat F s) ⊗[S.presheaf.stalk s] Rh)
        (IsLocalRing.maximalIdeal Rh) := sorry

/-- A point is weakly associated to a quasi-coherent module if and only if the maximal ideal
of a strict henselization is weakly associated to the scalar-extended stalk. -/
theorem mem_weakAss_iff_strictHenselization
    {S : Scheme.{u}} (s : S) (F : S.Modules) [F.IsQuasicoherent]
    (Rsh : Type v) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh] :
    s ∈ F.weakAss ↔
      Ideal.IsWeaklyAssociatedToModule Rsh
        ((RingedSpace.stalkModuleCat F s) ⊗[S.presheaf.stalk s] Rsh)
        (IsLocalRing.maximalIdeal Rsh) := sorry

/-- Weak association at a scheme point is equivalent to weak association of the stalk maximal
ideal before scalar extension, after henselization, and after strict henselization. -/
@[stacks 0CTU]
theorem mem_weakAss_henselization_tfae
    {S : Scheme.{u}} (s : S) (F : S.Modules) [F.IsQuasicoherent]
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh] :
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
        (IsLocalRing.maximalIdeal Rsh)] := sorry

end AlgebraicGeometry.Scheme.Modules
