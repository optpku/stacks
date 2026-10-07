module

public import ReasLib.LinearAlgebra.Determinant.Projective
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

noncomputable section

universe u v

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The trace computed after extending an endomorphism to a split finite-free presentation
and projecting back to its finite-projective summand is additive. -/
theorem trace_splitFreePresentation_add
    (p : SplitFreePresentation R M) (f g : M →ₗ[R] M) :
    trace R (Fin p.rank → R) (p.iota ∘ₗ (f + g) ∘ₗ p.pi) =
      trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi) +
        trace R (Fin p.rank → R) (p.iota ∘ₗ g ∘ₗ p.pi) := sorry

/-- The trace computed after extending an endomorphism to a split finite-free presentation
and projecting back to its finite-projective summand is homogeneous. -/
theorem trace_splitFreePresentation_smul
    (p : SplitFreePresentation R M) (r : R) (f : M →ₗ[R] M) :
    trace R (Fin p.rank → R) (p.iota ∘ₗ (r • f) ∘ₗ p.pi) =
      r • trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi) := sorry

/-- The trace of finite-projective endomorphisms computed in a fixed split finite-free
presentation. -/
def traceOfSplitFreePresentation (p : SplitFreePresentation R M) :
    (M →ₗ[R] M) →ₗ[R] R where
  toFun f := trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi)
  map_add' := trace_splitFreePresentation_add p
  map_smul' := trace_splitFreePresentation_smul p

/-- The trace computed from a finite-projective split presentation does not depend on the
presentation. -/
theorem traceOfSplitFreePresentation_independent
    (p q : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    traceOfSplitFreePresentation p f = traceOfSplitFreePresentation q f := sorry

/-- The basis-free trace linear map on endomorphisms of a finite-projective module. -/
noncomputable def projectiveTrace : (M →ₗ[R] M) →ₗ[R] R :=
  traceOfSplitFreePresentation (splitFreePresentation R M)

/-- `projectiveTrace` can be computed using any split finite-free presentation. -/
theorem projectiveTrace_apply (p : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    projectiveTrace f =
      trace R (Fin p.rank → R) (p.iota ∘ₗ f ∘ₗ p.pi) := sorry

/-- On a finite free module, `projectiveTrace` agrees with the ordinary basis-defined trace. -/
theorem projectiveTrace_eq_trace [Module.Free R M] :
    projectiveTrace = trace R M := sorry

end LinearMap

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Projective R S]

/-- The algebra trace of a finite-projective algebra, defined without choosing a basis. -/
noncomputable def finiteProjectiveTrace : S →ₗ[R] R :=
  LinearMap.projectiveTrace.comp (Algebra.lmul R S).toLinearMap

/-- The finite-projective algebra trace is the projective trace of left multiplication. -/
theorem finiteProjectiveTrace_apply (s : S) :
    finiteProjectiveTrace R S s =
      LinearMap.projectiveTrace (Algebra.lmul R S s) := sorry

/-- For a finite free algebra, the finite-projective trace agrees with `Algebra.trace`. -/
theorem finiteProjectiveTrace_eq_trace [Module.Free R S] :
    finiteProjectiveTrace R S = Algebra.trace R S := sorry

end Algebra

namespace Module

/-- A finite flat module over a Noetherian ring is projective. -/
theorem projective_of_finite_flat
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] :
    Module.Projective R M := sorry

end Module
