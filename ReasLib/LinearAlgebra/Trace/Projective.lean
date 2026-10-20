module

public import ReasLib.LinearAlgebra.Determinant.Projective
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

noncomputable section

universe u v

namespace LinearMap.FiniteProjective

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The trace computed in a split finite-free presentation is additive in the
endomorphism. -/
theorem traceOfPresentation_add
    (p : LinearMap.SplitFreePresentation R M) (f g : M →ₗ[R] M) :
    LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ (f + g) ∘ₗ p.pi) =
      LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi) +
        LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ g ∘ₗ p.pi) := sorry

/-- The trace computed in a split finite-free presentation is homogeneous in
the endomorphism. -/
theorem traceOfPresentation_smul
    (p : LinearMap.SplitFreePresentation R M) (r : R) (f : M →ₗ[R] M) :
    LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ (r • f) ∘ₗ p.pi) =
      r • LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi) := sorry

/-- The trace of finite-projective endomorphisms computed in a fixed split
finite-free presentation. -/
def traceOfPresentation (p : LinearMap.SplitFreePresentation R M) :
    (M →ₗ[R] M) →ₗ[R] R where
  toFun f := LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi)
  map_add' := traceOfPresentation_add p
  map_smul' := traceOfPresentation_smul p

/-- The trace of an endomorphism computed from a split finite-free presentation
is independent of the presentation. -/
theorem traceOfPresentation_independent
    (p q : LinearMap.SplitFreePresentation R M) (f : M →ₗ[R] M) :
    traceOfPresentation p f = traceOfPresentation q f := sorry

/-- The basis-free trace linear map on endomorphisms of a finite-projective
module. -/
noncomputable def trace : (M →ₗ[R] M) →ₗ[R] R :=
  traceOfPresentation (LinearMap.splitFreePresentation R M)

/-- The finite-projective trace can be computed in any split finite-free
presentation. -/
theorem trace_apply (p : LinearMap.SplitFreePresentation R M) (f : M →ₗ[R] M) :
    trace f =
      LinearMap.trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi) := sorry

/-- On a finite free module, the finite-projective trace agrees with the
ordinary basis-defined trace. -/
theorem trace_eq_trace [Module.Free R M] :
    trace = LinearMap.trace R M := sorry

end LinearMap.FiniteProjective

namespace Algebra.FiniteProjective

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Projective R S]

/-- The algebra trace of a finite-projective algebra, defined without choosing
a basis. -/
noncomputable def trace : S →ₗ[R] R :=
  LinearMap.FiniteProjective.trace.comp (Algebra.lmul R S).toLinearMap

/-- The finite-projective algebra trace is the finite-projective trace of left
multiplication. -/
theorem trace_apply (s : S) :
    trace R S s = LinearMap.FiniteProjective.trace (Algebra.lmul R S s) := sorry

/-- For a finite free algebra, the finite-projective trace agrees with
`Algebra.trace`. -/
theorem trace_eq_trace [Module.Free R S] :
    trace R S = Algebra.trace R S := sorry

end Algebra.FiniteProjective

namespace Module

/-- A finite flat module over a Noetherian ring is projective. -/
theorem projectiveOfFiniteFlat
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] :
    Module.Projective R M := sorry

end Module

end
