module

public import Mathlib.Algebra.Module.Injective

@[expose] public section

universe u v

/-- An `R`-module `Q` is injective if and only if every `R`-linear map from an ideal of `R`
to `Q` extends to an `R`-linear map from `R` to `Q`. -/
theorem Module.Injective.iff_baer {R : Type u} [Ring R] {Q : Type v}
    [AddCommGroup Q] [Module R Q] [Small.{v, u} R] :
    Module.Injective R Q ↔ Module.Baer R Q :=
  Module.Baer.iff_injective.symm
