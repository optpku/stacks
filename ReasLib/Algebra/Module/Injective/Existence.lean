module

public import ReasLib.Algebra.Module.Injective.Hull

@[expose] public section

universe u v

/-- Every module over a ring admits an injective hull. -/
theorem Module.exists_isInjectiveHull
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (I : Type (max u v)) (_ : AddCommGroup I) (_ : Module R I)
      (_ : Module.Injective R I) (f : M →ₗ[R] I), f.IsInjectiveHull := sorry
