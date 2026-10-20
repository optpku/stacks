/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients of restricted-scalar modules

The `RestrictScalars` wrapper is intentionally opaque, so the generic submodule quotient
instances do not match it by reduction.  This leaf supplies the canonical quotient carrier and
the quotient-ring module instance once, allowing tower statements to stay in the direct
mathematical notation used downstream.
-/

@[expose] public section

universe u v w

namespace RestrictScalars

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommRing R] [Semiring S] [AddCommGroup M] [Module S M] [Algebra R S]

/-- Stacks `00DV`: a restricted-scalar module has its canonical quotient by an `R`-submodule. -/
@[stacks 00DV "restricted-scalar quotient carrier"]
instance hasQuotient :
    HasQuotient (RestrictScalars R S M)
      (Submodule R (RestrictScalars R S M)) :=
  ⟨fun p =>
    Quotient (@Submodule.quotientRel R (RestrictScalars R S M)
      (inferInstance : Ring R) (inferInstance : AddCommGroup (RestrictScalars R S M))
      (inferInstance : Module R (RestrictScalars R S M)) p)⟩

/-- Stacks `00DV`: quotienting a restricted-scalar module by `I` carries the canonical
`R ⧸ I`-module structure. -/
@[stacks 00DV "restricted-scalar quotient module"]
instance quotientModule (I : Ideal R) :
    Module (R ⧸ I)
      ((RestrictScalars R S M) ⧸
        (I • (⊤ : Submodule R (RestrictScalars R S M)))) :=
  (@Module.isTorsionBySet_quotient_ideal_smul R (RestrictScalars R S M)
    (inferInstance : Ring R) (inferInstance : AddCommGroup (RestrictScalars R S M))
    (inferInstance : Module R (RestrictScalars R S M)) I).module

end RestrictScalars
