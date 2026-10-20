module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Ideal.Colon

@[expose] public section

universe u v

namespace Module.Invertible

/-- For an invertible module, the annihilator of the quotient by the span of an
element is the range of evaluation at that element. -/
theorem annihilator_quotient_span_eq_range_eval
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] (τ : M) :
    Module.annihilator R (M ⧸ Submodule.span R {τ}) =
      (Module.Dual.eval R M τ).range := sorry

end Module.Invertible
