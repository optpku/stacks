/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.MvPolynomial.Localization.GenericFiber

/-!
# Modules on Polynomial Generic Fibers

This leaf fixes the coefficient-fraction-field action on the generic-fiber
localization of a multivariate polynomial module.  The action and its free
module instance are scoped because the localized carrier also has its direct
polynomial-localization scalar presentation.

@stack 051T
-/

@[expose] public section

universe u v w

namespace MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A] [IsDomain A]
variable {N : Type w} [AddCommGroup N] [Module (MvPolynomial σ A) N]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: the coefficient fraction field acts on the generic-fiber
localization of a polynomial module by restriction of scalars. -/
@[reducible, stacks 051T "polynomial generic-fiber module action"]
noncomputable def genericFiberModule :
    Module (Localization (nonZeroDivisors A))
      (LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A)) N) :=
  Module.compHom
    (LocalizedModule
      (Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A)) N)
    (algebraMap (Localization (nonZeroDivisors A))
      (Localization
        (Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A))))

/-- Tag `051T`: the generic fiber of every multivariate polynomial module is
free over the fraction field of the coefficient domain. -/
@[stacks 051T "polynomial module generic-fiber freeness"]
theorem genericFiber_free :
    letI : Module (Localization (nonZeroDivisors A))
        (LocalizedModule
          (Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A)) N) :=
      genericFiberModule (σ := σ) (N := N)
    Module.Free (Localization (nonZeroDivisors A))
      (LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A)) N) := sorry

end MvPolynomial.Localization

/-! The generic-fiber scalar presentation is enabled only together with the
other normalized multivariate-polynomial localization actions. -/
scoped[MvPolynomial.Localization] attribute [instance 100]
  MvPolynomial.Localization.genericFiberModule
  MvPolynomial.Localization.genericFiber_free

section

open scoped MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A] [IsDomain A]
variable {N : Type w} [AddCommGroup N] [Module (MvPolynomial σ A) N]

attribute [local instance] MvPolynomial.algebraMvPolynomial

#synth Module.Free (Localization (nonZeroDivisors A))
  (LocalizedModule
    (Algebra.algebraMapSubmonoid (MvPolynomial σ A) (nonZeroDivisors A)) N)

end
