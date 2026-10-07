module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.RingTheory.GenericFlatness.FiniteType

@[expose] public section

universe uR uA uB uM uN

namespace LinearMap

/-- For finite-type maps `R → A → B` from a Noetherian domain and an `A`-linear map from
a finite `A`-module to a finite `B`-module, its cokernel becomes flat over `R` after
inverting a suitable nonzero element of `R`. -/
@[stacks 0H40]
theorem exists_nonzero_away_flat_coker
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Finite A M]
    {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [Module B N]
    [IsScalarTower R A N] [IsScalarTower A B N] [Module.Finite B N]
    (φ : M →ₗ[A] N) :
    ∃ f : R, f ≠ 0 ∧
      Module.Flat (Localization.Away f)
        (LocalizedModule.Away f N ⧸ LinearMap.range
          (LocalizedModule.map (Submonoid.powers f) (φ.restrictScalars R))) := sorry

end LinearMap
