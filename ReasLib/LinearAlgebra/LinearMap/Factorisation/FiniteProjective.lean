module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.LinearMap.Factorisation.Projective
public import ReasLib.RingTheory.Finiteness.Projective

@[expose] public section

/-!
# Linear maps factoring through finite projective modules

@stack 0G91
-/

universe u v w

namespace LinearMap

section Semiring

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

namespace Factorisation

/-- A linear-map factorisation with a finite projective midpoint. -/
@[stacks 0G91 "structured finite-projective factorisation"]
structure FiniteProjective (f : M →ₗ[R] N) where
  /-- The underlying factorisation. -/
  base : Factorisation f
  /-- Finite projectivity of the selected midpoint. -/
  property : Module.FiniteProjective R base.mid

namespace FiniteProjective

variable {f : M →ₗ[R] N}

/-- Build a finite-projective factorisation from a finite-projective midpoint and two maps. -/
@[stacks 0G91 "constructor for finite-projective factorisations"]
def ofMaps (P : Type (max u v w)) [AddCommMonoid P] [Module R P]
    (property : Module.FiniteProjective R P) (fromSource : M →ₗ[R] P)
    (toTarget : P →ₗ[R] N) (factor : toTarget.comp fromSource = f) :
    FiniteProjective f where
  base :=
    { mid := SemimoduleCat.of R P
      fromSource := fromSource
      toTarget := toTarget
      factor := factor }
  property := property

/-- The midpoint of a finite-projective factorisation. -/
@[stacks 0G91 "midpoint of a finite-projective factorisation"]
abbrev mid (F : FiniteProjective f) := F.base.mid

/-- The midpoint of a finite-projective factorisation is finite. -/
@[stacks 0G91 "finiteness of the factorisation midpoint"]
abbrev finite (F : FiniteProjective f) : Module.Finite R F.mid := F.property.finite

/-- The midpoint of a finite-projective factorisation is projective. -/
@[stacks 0G91 "projectivity of the factorisation midpoint"]
abbrev projective (F : FiniteProjective f) : Module.Projective R F.mid := F.property.projective

/-- The source map of a finite-projective factorisation. -/
@[stacks 0G91 "source map of a finite-projective factorisation"]
abbrev fromSource (F : FiniteProjective f) : M →ₗ[R] F.mid := F.base.fromSource

/-- The target map of a finite-projective factorisation. -/
@[stacks 0G91 "target map of a finite-projective factorisation"]
abbrev toTarget (F : FiniteProjective f) : F.mid →ₗ[R] N := F.base.toTarget

/-- The triangle equation of a finite-projective factorisation. -/
theorem factor (F : FiniteProjective f) : F.toTarget.comp F.fromSource = f := sorry

/-- Forget finiteness from a finite-projective factorisation. -/
@[stacks 0G91 "finite-projective factorisation as projective"]
def toProjective (F : FiniteProjective f) : Factorisation.Projective f where
  base := F.base
  projective := F.property.projective

end FiniteProjective

end Factorisation

/-- A linear map factors through a finite projective module. -/
@[stacks 0G91 "factorisation through a finite projective module"]
abbrev FactorsThroughFiniteProjective (f : M →ₗ[R] N) : Prop :=
  Nonempty (Factorisation.FiniteProjective f)

/-- The zero map factors through a finite projective module. -/
theorem factorsThroughFiniteProjective_zero :
    FactorsThroughFiniteProjective (0 : M →ₗ[R] N) := sorry

/-- Finite-projective-factor maps are closed under addition. -/
theorem FactorsThroughFiniteProjective.add {f g : M →ₗ[R] N}
    (hf : f.FactorsThroughFiniteProjective) (hg : g.FactorsThroughFiniteProjective) :
    (f + g).FactorsThroughFiniteProjective := sorry

/-- A finite-projective factorisation is a projective factorisation. -/
theorem FactorsThroughFiniteProjective.projective {f : M →ₗ[R] N}
    (hf : f.FactorsThroughFiniteProjective) : f.FactorsThroughProjective := sorry

/-- For a finite source, a projective factorisation can be chosen finite projective. -/
@[stacks 0G91]
theorem FactorsThroughProjective.finite [Module.Finite R M] {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) : f.FactorsThroughFiniteProjective := sorry

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Finite-projective-factor maps are closed under scalar multiplication. -/
theorem FactorsThroughFiniteProjective.smul (r : R) {f : M →ₗ[R] N}
    (hf : f.FactorsThroughFiniteProjective) :
    (r • f).FactorsThroughFiniteProjective := sorry

/-- The submodule of maps which factor through a finite projective module. -/
@[stacks 0G91 "finite-projective-factor submodule"]
def finiteProjectiveFactors : Submodule R (M →ₗ[R] N) where
  carrier := FactorsThroughFiniteProjective
  zero_mem' := factorsThroughFiniteProjective_zero
  add_mem' := FactorsThroughFiniteProjective.add
  smul_mem' := FactorsThroughFiniteProjective.smul

/-- Membership in `finiteProjectiveFactors` is finite-projective factorisation. -/
theorem mem_finiteProjectiveFactors (f : M →ₗ[R] N) :
    f ∈ finiteProjectiveFactors (R := R) (M := M) (N := N) ↔
      f.FactorsThroughFiniteProjective := sorry

/-- For a finite source, projective-factor and finite-projective-factor submodules agree. -/
@[stacks 0G91 "submodule form"]
theorem projectiveFactors_eq_finiteProjectiveFactors [Module.Finite R M] :
    projectiveFactors (R := R) (M := M) (N := N) =
      finiteProjectiveFactors (R := R) (M := M) (N := N) := sorry

end CommSemiring

end LinearMap
