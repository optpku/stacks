/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.LinearMap.Factorisation

@[expose] public section

/-!
# Linear maps factoring through projective modules

Projective and free factorisations retain their midpoint property on the chosen factorisation.
Their existence is exposed as a proposition, and the projective ones form a canonical submodule
of the linear hom module.

@stack 0G90
-/

universe u v w v' w'

namespace LinearMap

section Semiring

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']
variable {N' : Type w'} [AddCommMonoid N'] [Module R N']

namespace Factorisation

/-- A linear-map factorisation with a projective midpoint. -/
@[stacks 0G90 "structured projective factorisation"]
structure Projective (f : M →ₗ[R] N) where
  /-- The underlying factorisation. -/
  base : Factorisation f
  /-- Projectivity of the selected midpoint. -/
  projective : Module.Projective R base.mid

/-- A linear-map factorisation with a free midpoint. -/
@[stacks 0G90 "structured free factorisation"]
abbrev Free (f : M →ₗ[R] N) :=
  { factorisation : Factorisation f // Module.Free R factorisation.mid }

namespace Projective

variable {f : M →ₗ[R] N}

/-- Build a projective factorisation from a projective midpoint and two maps. -/
@[stacks 0G90 "constructor for projective factorisations"]
def ofMaps (P : Type (max u v w)) [AddCommMonoid P] [Module R P]
    [Module.Projective R P] (fromSource : M →ₗ[R] P) (toTarget : P →ₗ[R] N)
    (factor : toTarget.comp fromSource = f) : Projective f where
  base :=
    { mid := SemimoduleCat.of R P
      fromSource := fromSource
      toTarget := toTarget
      factor := factor }
  projective := inferInstance

/-- The midpoint of a projective factorisation. -/
@[stacks 0G90 "midpoint of a projective factorisation"]
abbrev mid (F : Projective f) := F.base.mid

/-- The source map of a projective factorisation. -/
@[stacks 0G90 "source map of a projective factorisation"]
abbrev fromSource (F : Projective f) : M →ₗ[R] F.mid := F.base.fromSource

/-- The target map of a projective factorisation. -/
@[stacks 0G90 "target map of a projective factorisation"]
abbrev toTarget (F : Projective f) : F.mid →ₗ[R] N := F.base.toTarget

/-- The triangle equation of a projective factorisation. -/
theorem factor (F : Projective f) : F.toTarget.comp F.fromSource = f := sorry

end Projective

namespace Free

variable {f : M →ₗ[R] N}

/-- The underlying factorisation of a free factorisation. -/
abbrev base (F : Free f) : Factorisation f := F.val

/-- The selected midpoint of a free factorisation is free. -/
abbrev free (F : Free f) : Module.Free R F.base.mid := F.property

/-- Build a free factorisation from a free midpoint and two maps. -/
@[stacks 0G90 "constructor for free factorisations"]
def ofMaps (P : Type (max u v w)) [AddCommMonoid P] [Module R P]
    [Module.Free R P] (fromSource : M →ₗ[R] P) (toTarget : P →ₗ[R] N)
    (factor : toTarget.comp fromSource = f) : Free f :=
  ⟨Factorisation.ofMaps P fromSource toTarget factor, (inferInstance : Module.Free R P)⟩

/-- The midpoint of a free factorisation. -/
@[stacks 0G90 "midpoint of a free factorisation"]
abbrev mid (F : Free f) := F.base.mid

/-- The source map of a free factorisation. -/
@[stacks 0G90 "source map of a free factorisation"]
abbrev fromSource (F : Free f) : M →ₗ[R] F.mid := F.base.fromSource

/-- The target map of a free factorisation. -/
@[stacks 0G90 "target map of a free factorisation"]
abbrev toTarget (F : Free f) : F.mid →ₗ[R] N := F.base.toTarget

/-- The triangle equation of a free factorisation. -/
theorem factor (F : Free f) : F.toTarget.comp F.fromSource = f := sorry

/-- Forget freeness while retaining the induced projective factorisation. -/
@[stacks 0G90 "free factorisation as a projective factorisation"]
def toProjective (F : Free f) : Projective f where
  base := F.base
  projective := @Module.Projective.of_free R _ (F.base.mid : Type _) _ _ F.free

end Free

end Factorisation

/-- A linear map factors through a projective module. -/
@[stacks 0G90 "factorisation through a projective module"]
abbrev FactorsThroughProjective (f : M →ₗ[R] N) : Prop :=
  Nonempty (Factorisation.Projective f)

/-- A linear map factors through a free module. -/
@[stacks 0G90 "factorisation through a free module"]
abbrev FactorsThroughFree (f : M →ₗ[R] N) : Prop :=
  Nonempty (Factorisation.Free f)

/-- The zero map factors through a projective module. -/
theorem factorsThroughProjective_zero :
    FactorsThroughProjective (0 : M →ₗ[R] N) := sorry

/-- Every map with projective source factors through a projective module. -/
theorem FactorsThroughProjective.of_projective_source (f : M →ₗ[R] N)
    [Module.Projective R M] : f.FactorsThroughProjective := sorry

/-- Every map with projective target factors through a projective module. -/
theorem FactorsThroughProjective.of_projective_target (f : M →ₗ[R] N)
    [Module.Projective R N] : f.FactorsThroughProjective := sorry

/-- Projective-factor maps are closed under addition. -/
theorem FactorsThroughProjective.add {f g : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) (hg : g.FactorsThroughProjective) :
    (f + g).FactorsThroughProjective := sorry

/-- A free factorisation is a projective factorisation. -/
theorem FactorsThroughFree.projective {f : M →ₗ[R] N}
    (hf : f.FactorsThroughFree) : f.FactorsThroughProjective := sorry

/-- A projective factorisation can be refined to a free factorisation. -/
theorem FactorsThroughProjective.free {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) : f.FactorsThroughFree := sorry

/-- Factorisation through a projective module is equivalent to factorisation through a free module. -/
@[stacks 0G90 "(1), projective versus free factorisation"]
theorem FactorsThroughProjective.iff_free (f : M →ₗ[R] N) :
    f.FactorsThroughProjective ↔ f.FactorsThroughFree := sorry

/-- Projective factorisation is stable under precomposition. -/
theorem FactorsThroughProjective.precomp {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) (g : M' →ₗ[R] M) :
    (f.comp g).FactorsThroughProjective := sorry

/-- Projective factorisation is stable under postcomposition. -/
theorem FactorsThroughProjective.postcomp {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) (g : N →ₗ[R] N') :
    (g.comp f).FactorsThroughProjective := sorry

/-- Arbitrary pre- and postcomposition preserve projective factorisation. -/
@[stacks 0G90 "(3), composition stability"]
theorem FactorsThroughProjective.comp {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) (g : M' →ₗ[R] M) (h : N →ₗ[R] N') :
    (h.comp (f.comp g)).FactorsThroughProjective := sorry

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Projective-factor maps are closed under scalar multiplication. -/
theorem FactorsThroughProjective.smul (r : R) {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) : (r • f).FactorsThroughProjective := sorry

/-- The submodule of linear maps which factor through a projective module. -/
@[stacks 0G90 "(2), projective-factor submodule"]
def projectiveFactors : Submodule R (M →ₗ[R] N) where
  carrier := FactorsThroughProjective
  zero_mem' := factorsThroughProjective_zero
  add_mem' := FactorsThroughProjective.add
  smul_mem' := FactorsThroughProjective.smul

/-- Membership in `projectiveFactors` is factorisation through a projective module. -/
theorem mem_projectiveFactors (f : M →ₗ[R] N) :
    f ∈ projectiveFactors (R := R) (M := M) (N := N) ↔ f.FactorsThroughProjective := sorry

end CommSemiring

end LinearMap
