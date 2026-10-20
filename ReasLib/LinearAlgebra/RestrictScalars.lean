/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of Restriction of Scalars

This file provides the elementary map API for Mathlib's `RestrictScalars` type
alias.  The alias keeps the restricted module action canonical and prevents
instance diamonds in downstream statements.

@stack 0H1C
-/

@[expose] public section

namespace RestrictScalars

universe uR uS uM uN uP

variable {R : Type uR} {S : Type uS}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module S M] [Module S N] [Module S P]

/-- An `S`-linear map, viewed functorially between the canonical restrictions
of scalars to `R`. -/
@[stacks 0H1C "functorial restriction of scalars"]
def map (f : M →ₗ[S] N) :
    RestrictScalars R S M →ₗ[R] RestrictScalars R S N where
  toFun x := (addEquiv R S N).symm (f (addEquiv R S M x))
  map_add' x y := by
    apply (addEquiv R S N).injective
    simp
  map_smul' r x := by
    apply (addEquiv R S N).injective
    simp [addEquiv_map_smul]

/-- Restriction of scalars preserves the value of a linear map. -/
@[simp]
theorem map_apply (f : M →ₗ[S] N) (x : RestrictScalars R S M) :
    map (R := R) (S := S) f x = f x :=
  rfl

/-- Restriction of scalars sends the identity linear map to the identity. -/
@[simp]
theorem map_id :
    map (R := R) (S := S) (LinearMap.id : M →ₗ[S] M) = LinearMap.id :=
  rfl

/-- Restriction of scalars preserves composition of linear maps. -/
@[simp]
theorem map_comp (g : N →ₗ[S] P) (f : M →ₗ[S] N) :
    map (R := R) (S := S) (g.comp f) =
      (map (R := R) (S := S) g).comp (map (R := R) (S := S) f) :=
  rfl

/-- An `S`-submodule, viewed as an `R`-submodule of the canonical restriction
of scalars.  Unlike `Submodule.restrictScalars`, this formulation does not ask
for a second module structure on the original carrier. -/
@[stacks 0H1C "submodules of a canonical restriction of scalars"]
def submodule (p : Submodule S M) : Submodule R (RestrictScalars R S M) where
  carrier := {x | addEquiv R S M x ∈ p}
  zero_mem' := p.zero_mem
  add_mem' hx hy := p.add_mem hx hy
  smul_mem' r _ hx := p.smul_mem (algebraMap R S r) hx

/-- Membership in a restricted submodule is membership in the original submodule. -/
@[simp]
theorem mem_submodule (p : Submodule S M) (x : RestrictScalars R S M) :
    x ∈ submodule (R := R) (S := S) p ↔ addEquiv R S M x ∈ p :=
  Iff.rfl

/-- The `S`-span of a set, regarded canonically as an `R`-submodule after
restriction of scalars. -/
@[stacks 0H1C "span after canonical restriction of scalars"]
def span (s : Set M) : Submodule R (RestrictScalars R S M) :=
  submodule (R := R) (S := S) (Submodule.span S s)

/-- Membership in the restricted span is membership in the original scalar span. -/
@[simp]
theorem mem_span (s : Set M) (x : RestrictScalars R S M) :
    x ∈ span (R := R) (S := S) s ↔ addEquiv R S M x ∈ Submodule.span S s :=
  Iff.rfl

/-- Restriction of scalars preserves the kernel of a linear map. -/
@[simp]
theorem ker_map (f : M →ₗ[S] N) :
    (map (R := R) (S := S) f).ker =
      submodule (R := R) (S := S) f.ker := by
  ext x
  rfl

end RestrictScalars
