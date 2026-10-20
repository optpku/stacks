/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.LocallyFinite
public import ReasLib.Algebra.Module.Graded.Basic
public import ReasLib.Algebra.Module.EulerPoincare
public import ReasLib.Algebra.Module.Graded.Hilbert
import StacksCheckRecall

@[expose] public section

universe u v

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/- Definition 111.26.2 (1): a graded module over a ring `A` is an `A`-module `M` endowed with a
direct-sum decomposition `⨁ n, ℳ n` into `A`-submodules `ℳ : ℤ → Submodule A M`. This is the
source-level owner `GradedModule.Decomposition`, definitionally backed by `DirectSum.Decomposition`. -/
@[stacks 027Y]
#check (GradedModule.Decomposition : (ℤ → Submodule A M) → Type v)

/- Definition 111.26.2 (2): a graded module is locally finite when every degree piece is a finite
`A`-module. This is the owner `GradedModule.LocallyFinite`. -/
@[stacks 027Y]
#check (GradedModule.LocallyFinite : (ℤ → Submodule A M) → Prop)

/- Definition 111.26.2 (3): an Euler-Poincaré function on finite `A`-modules assigns an integer to
every finite module and is additive on short exact sequences. This is the owner
`Module.EulerPoincareFunction`. -/
@[stacks 027Y]
#check (Module.EulerPoincareFunction.{u, v} :
  (A : Type u) → [CommRing A] → Type (max u (v + 1)))

variable [IsNoetherianRing A]

/- Definition 111.26.2 (4): the Hilbert function of a locally finite graded module `M` with respect
to an Euler-Poincaré function `φ` is `χ_φ(M, n) = φ(M_n)`, owned by `GradedModule.hilbertFunction`. -/
@[stacks 027Y]
#check (GradedModule.hilbertFunction :
  (φ : Module.EulerPoincareFunction.{u, v} A) → (ℳ : ℤ → Submodule A M) →
    [GradedModule.Decomposition ℳ] → [GradedModule.LocallyFinite ℳ] → ℤ → ℤ)

/- Definition 111.26.2 (5): a locally finite graded module has a Hilbert polynomial when its
Hilbert function agrees with a numerical polynomial for all sufficiently large `n`. This is the
owner `GradedModule.HasHilbertPolynomial`. -/
@[stacks 027Y]
#check (GradedModule.HasHilbertPolynomial :
  (φ : Module.EulerPoincareFunction.{u, v} A) → (ℳ : ℤ → Submodule A M) →
    [GradedModule.Decomposition ℳ] → [GradedModule.LocallyFinite ℳ] → Prop)
