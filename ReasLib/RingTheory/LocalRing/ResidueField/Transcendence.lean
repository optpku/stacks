module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Transcendence degree of residue-field extensions

This module packages the residue-field extension induced by a prime `P` lying over a prime `p`.
The algebra structure is named but deliberately not an instance: its ambient local-ring
construction is non-global in mathlib to avoid instance diamonds.
-/

namespace Ideal.ResidueField

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- An algebraic residue-field extension preserves transcendence degree over every compatible
base algebra after lifting the two cardinal values to a common universe. -/
theorem lift_trdeg_eq_of_isAlgebraic
    {K : Type w} [CommRing K] [Algebra K R] [Algebra K S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [Algebra p.ResidueField P.ResidueField]
    [IsScalarTower K p.ResidueField P.ResidueField]
    [Algebra.IsAlgebraic p.ResidueField P.ResidueField] :
    Cardinal.lift.{v} (Algebra.trdeg K p.ResidueField) =
      Cardinal.lift.{u} (Algebra.trdeg K P.ResidueField) := sorry

/-- The natural-number view of transcendence degree is unchanged by an algebraic
residue-field extension over a compatible base algebra. -/
theorem trdegToNat_eq_of_isAlgebraic
    {K : Type w} [CommRing K] [Algebra K R] [Algebra K S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [Algebra p.ResidueField P.ResidueField]
    [IsScalarTower K p.ResidueField P.ResidueField]
    [Algebra.IsAlgebraic p.ResidueField P.ResidueField] :
    Cardinal.toNat (Algebra.trdeg K p.ResidueField) =
      Cardinal.toNat (Algebra.trdeg K P.ResidueField) := sorry

/-- A quasi-finite algebra preserves transcendence degree over every compatible base algebra
after lifting the two cardinal values to a common universe. -/
theorem lift_trdeg_eq_of_quasiFinite
    {K : Type w} [CommRing K] [Algebra K R] [Algebra K S] [IsScalarTower K R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [Algebra.QuasiFinite R S] :
    Cardinal.lift.{v} (Algebra.trdeg K p.ResidueField) =
      Cardinal.lift.{u} (Algebra.trdeg K P.ResidueField) := sorry

/-- A quasi-finite algebra preserves the natural-number view of residue-field transcendence
degree over every compatible base algebra. -/
theorem trdegToNat_eq_of_quasiFinite
    {K : Type w} [CommRing K] [Algebra K R] [Algebra K S] [IsScalarTower K R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [Algebra.QuasiFinite R S] :
    Cardinal.toNat (Algebra.trdeg K p.ResidueField) =
      Cardinal.toNat (Algebra.trdeg K P.ResidueField) := sorry

/-- The cardinal-valued transcendence degree of the residue-field extension induced by
`P.LiesOver p`. -/
noncomputable def trdeg (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] : Cardinal :=
  -- Local instance justification (instance diamond): this is the named residue-field algebra
  -- selected by the definition and must not participate in ambient instance search.
  letI : Algebra p.ResidueField P.ResidueField := algebraOfLiesOver p P
  Algebra.trdeg p.ResidueField P.ResidueField

/-- The natural-number `Cardinal.toNat` view of `Ideal.ResidueField.trdeg`.

As with every `Cardinal.toNat` projection, this value is `0` for infinite transcendence degree. -/
noncomputable def trdegToNat (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] : ℕ :=
  Cardinal.toNat (trdeg p P)

end Ideal.ResidueField
