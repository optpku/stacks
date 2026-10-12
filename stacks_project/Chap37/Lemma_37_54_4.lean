/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GenericFlatness.Cokernel
import StacksCheckRecall

@[expose] public section

universe uR uA uB uM uN

/- Lemma 37.54.4: for finite-type maps `R → A → B` from a Noetherian domain and
an `A`-linear map from a finite `A`-module to a finite `B`-module, the cokernel
becomes flat over `R` after inverting a suitable nonzero element of `R`. -/
@[stacks 0H40] #check (LinearMap.exists_nonzero_away_flat_coker :
  ∀
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Finite A M]
    {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [Module B N]
    [IsScalarTower R A N] [IsScalarTower A B N] [Module.Finite B N]
    (φ : M →ₗ[A] N),
    ∃ f : R, f ≠ 0 ∧
      Module.Flat (Localization.Away f)
        (LocalizedModule.Away f N ⧸ LinearMap.range
          (LocalizedModule.map (Submonoid.powers f) (φ.restrictScalars R))))
