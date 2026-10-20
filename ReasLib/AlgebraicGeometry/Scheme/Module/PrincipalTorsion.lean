module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.Linear
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Kernel
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Quotient

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.PrincipalTorsion

/-- For an inverse system of scheme modules with quasi-coherent positive stages, the
stepwise short exact and power short exact conditions are equivalent to realization as
power kernels of a divisible module and as power quotients of a torsion-free module. -/
theorem conditions_tfae {X : Scheme.{u}}
    (f : RingedSpace.globalSectionsRing X.toRingedSpace)
    (F : SequentialInverseSystem X.Modules)
    (h_quasicoherent : ∀ n : ℕ, 1 ≤ n → (F.obj (op n)).IsQuasicoherent) :
    List.TFAE [
      CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented f F,
      CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPowerPresented f F,
      CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsKernelPresented f F,
      CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsQuotientPresented f F] := sorry

end AlgebraicGeometry.Scheme.Modules.PrincipalTorsion
