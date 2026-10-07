module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import ReasLib.RingTheory.Regular.JRing.FiniteFractionModel
public import ReasLib.RingTheory.Regular.JRing.FiniteTypeDomain
public import ReasLib.RingTheory.Regular.JRing.Quotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Equivalent criteria for J-2 rings

@stack 07PC

The three useful equivalences are exposed separately.  The four-way `TFAE`
is retained as a compact source-facing summary.
-/

universe u v

namespace IsJ2Ring

/-- A ring has residue models when every finite purely inseparable extension of a prime residue
field has a compatible finite `J-0` domain model with that fraction field. -/
@[stacks 07PC "finite J-0 models of purely inseparable residue extensions"]
def HasResidueModels (R : Type u) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
    Nonempty
      (IsJ0Ring.FiniteFractionModel
        ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField)))

/-- A Noetherian ring is `J-2` exactly when all of its finite type domain algebras are `J-0`.
This is one of the criteria in Lemma 15.47.6. -/
@[stacks 07PC "J-2 criterion by finite type domains"]
theorem iff_finiteType_domain_isJ0
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ2Ring.{u, v} R ↔
      ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A],
        IsJ0Ring A := sorry

/-- A Noetherian ring is `J-2` exactly when all of its finite algebras are `J-1`. This is one of
the criteria in Lemma 15.47.6. -/
@[stacks 07PC "J-2 criterion by finite algebras"]
theorem iff_finite_isJ1
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ2Ring.{u, v} R ↔
      ∀ (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A], IsJ1Ring A := sorry

/-- A Noetherian ring is `J-2` exactly when all finite purely inseparable extensions of its prime
residue fields have compatible finite `J-0` fraction-field models. This is one of the criteria in
Lemma 15.47.6. -/
@[stacks 07PC "J-2 criterion by residue-field models"]
theorem iff_hasResidueModels
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ2Ring.{u, v} R ↔ HasResidueModels.{u, v} R := sorry

/-- The `J-2`, finite-type-domain, finite-algebra, and residue-field-model conditions are
equivalent for a Noetherian ring. This is Lemma 15.47.6. -/
@[stacks 07PC "equivalent criteria for J-2 rings"]
theorem characterizations
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsJ2Ring.{u, v} R,
        ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A],
          IsJ0Ring A,
        ∀ (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A], IsJ1Ring A,
        HasResidueModels.{u, v} R ] := sorry

end IsJ2Ring
