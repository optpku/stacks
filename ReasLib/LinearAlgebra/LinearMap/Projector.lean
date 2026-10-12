/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear projectors

This leaf collects the small linear-algebra API shared by constructions that
represent a summand as the range of an idempotent endomorphism.  Mathlib owns
the underlying projection and projective-module notions; this file records
the ideal-multiple and intertwining consequences used by quotient arguments.
@stack 0BC5
-/

@[expose] public section

universe u v w

namespace LinearMap

section Split

variable {R : Type u} [Semiring R]
variable {P : Type v} [AddCommMonoid P] [Module R P]
variable {F : Type w} [AddCommMonoid F] [Module R F]

/-- The endomorphism of an ambient module induced by a split summand is idempotent. -/
@[stacks 07LV "split linear projector"]
theorem isIdempotentElem_comp_of_comp_eq_id
    (i : P →ₗ[R] F) (s : F →ₗ[R] P) (hs : s.comp i = LinearMap.id) :
    IsIdempotentElem (i.comp s) := sorry

/-- A split summand is linearly equivalent to the range of its ambient projector. -/
@[stacks 07LV "split summand as projector range"]
theorem nonempty_linearEquiv_range_comp_of_comp_eq_id
    (i : P →ₗ[R] F) (s : F →ₗ[R] P) (hs : s.comp i = LinearMap.id) :
    Nonempty (P ≃ₗ[R] LinearMap.range (i.comp s)) := sorry

/-- Subtracting the section component of a point lands in the kernel of a split surjection. -/
@[stacks 0BC5 "split-surjection kernel correction"]
theorem sub_section_mem_ker_of_comp_eq_id
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id) (z : P) :
    z - s (q z) ∈ LinearMap.ker q := sorry

/-- If a point lies in `I • ⊤`, its section-corrected kernel component comes from
`I • ⊤` inside the kernel. -/
@[stacks 0BC5 "ideal multiple in a split-surjection kernel"]
theorem sub_section_mem_map_smul_top_ker_of_comp_eq_id
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (I : Ideal R) (q : P →ₗ[R] Q) (s : Q →ₗ[R] P)
    (hs : q.comp s = LinearMap.id) {z : P} (hz : z ∈ I • (⊤ : Submodule R P)) :
    z - s (q z) ∈
      Submodule.map (LinearMap.ker q).subtype
        (I • (⊤ : Submodule R (LinearMap.ker q))) := sorry

end Split

section IdempotencyDefect

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The failure of an endomorphism to be idempotent. -/
@[stacks 07LV "idempotency defect"]
def idempotencyDefect (p : Module.End R M) : Module.End R M :=
  p.comp p - p

/-- An intertwining map kills the idempotency defect whenever the target endomorphism is
idempotent. -/
@[stacks 07LV "idempotency defect after intertwining"]
theorem comp_idempotencyDefect_eq_zero_of_intertwine
    (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hp' : p'.comp p' = p') (h : q.comp p = p'.comp q) :
    q.comp (idempotencyDefect p) = 0 := sorry

/-- Postcomposing an endomorphism already killed by a linear map keeps it killed. -/
@[stacks 07LV "linear map kills left product"]
theorem comp_mul_eq_zero_of_comp_eq_zero
    (q : M →ₗ[R] N) (d t : Module.End R M) (hd : q.comp d = 0) :
    q.comp (d * t) = 0 := sorry

end IdempotencyDefect

section IdealMultiples

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Pulling back an ambient ideal multiple along the subtype of a projected submodule gives its
intrinsic ideal multiple. -/
@[stacks 07LV "projected submodule ideal multiple"]
theorem IsProj.comap_smul_top_eq
    {p : Module.End R M} {U : Submodule R M} (hp : LinearMap.IsProj U p) (I : Ideal R) :
    Submodule.comap U.subtype (I • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R U) := sorry

/-- For an idempotent range, pulling back an ambient ideal multiple along the subtype gives the
intrinsic ideal multiple. -/
@[stacks 07LV "idempotent range ideal multiple"]
theorem IsIdempotentElem.comap_smul_top_eq
    {p : Module.End R M} (hp : IsIdempotentElem p) (I : Ideal R) :
    Submodule.comap (LinearMap.range p).subtype (I • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R (LinearMap.range p)) := sorry

end IdealMultiples

end LinearMap

namespace Module.Projective

section IdempotentRange

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A projected submodule of a projective module is projective. -/
@[stacks 07LV "projective projected submodule"]
theorem of_isProj [Module.Projective R M]
    {U : Submodule R M} {p : Module.End R M} (hp : LinearMap.IsProj U p) :
    Module.Projective R U := sorry

/-- The range of an idempotent endomorphism of a projective module is projective. -/
@[stacks 07LV "projective idempotent range"]
theorem range_of_isIdempotentElem [Module.Projective R M]
    (p : Module.End R M) (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) := sorry

end IdempotentRange

end Module.Projective
