module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Effective Cartier divisor approximations

This file owns finite weighted sums of effective Cartier divisors and the approximation relation
which records equality with a closed subscheme away from codimension two.
-/

@[expose] public section

open AlgebraicGeometry
open Set TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}
variable {ι : Type v}

/-- A subset of the underlying topological space of `X` has irreducible components of codimension
at least `k` if every maximal irreducible closed subset contained in it has `coheight` at least
`k`. -/
def irreducibleComponentsCodimAtLeast (k : ℕ) (F : Set X) : Prop :=
  ∀ Z : IrreducibleCloseds X,
    Maximal (fun Y : IrreducibleCloseds X ↦ (Y : Set X) ⊆ F) Z →
      (k : ℕ∞) ≤ Order.coheight Z

/-- A subset has irreducible components of codimension at least `k` exactly when each maximal
irreducible closed subset that it contains has `coheight` at least `k`. -/
theorem irreducibleComponentsCodimAtLeast_iff (k : ℕ) (F : Set X) :
    irreducibleComponentsCodimAtLeast k F ↔
      ∀ Z : IrreducibleCloseds X,
        Maximal (fun Y : IrreducibleCloseds X ↦ (Y : Set X) ⊆ F) Z →
          (k : ℕ∞) ≤ Order.coheight Z := sorry

/-- The finite weighted sum of a family of effective Cartier divisors, expressed as the product
of the corresponding powers of ideal-sheaf data. -/
def effectiveCartierDivisorWeightedSum (a : ι →₀ ℕ)
    (D : ι → X.IdealSheafData) : X.IdealSheafData :=
  a.prod (fun i n ↦ D i ^ n)

/-- A finite weighted sum of effective Cartier divisors is the `Finsupp` product of the
corresponding powers of ideal-sheaf data. -/
theorem effectiveCartierDivisorWeightedSum_def (a : ι →₀ ℕ)
    (D : ι → X.IdealSheafData) :
    effectiveCartierDivisorWeightedSum a D = a.prod (fun i n ↦ D i ^ n) := sorry

/-- Two closed subschemes of `X` agree away from codimension `2` if they coincide after
restriction to some open subscheme of `X` whose complement in the support of the second subscheme
has irreducible components of codimension at least `2`. -/
def agreesAwayFromCodimensionTwo (D Z : X.IdealSheafData) : Prop :=
  ∃ U : X.Opens,
    D.comap U.ι = Z.comap U.ι ∧
      irreducibleComponentsCodimAtLeast 2 (((Z.support : Set X) \ (U : Set X)) : Set X)

/-- Two closed subschemes agree away from codimension `2` exactly when they become equal on an
open subscheme whose omitted part of the second support has codimension at least `2`. -/
theorem agreesAwayFromCodimensionTwo_iff (D Z : X.IdealSheafData) :
    D.agreesAwayFromCodimensionTwo Z ↔
      ∃ U : X.Opens,
        D.comap U.ι = Z.comap U.ι ∧
          irreducibleComponentsCodimAtLeast 2 (((Z.support : Set X) \ (U : Set X)) : Set X) := sorry

/-- `D` is an effective Cartier divisor approximation to `Z` if it is an effective Cartier
divisor contained in `Z` and agreeing with `Z` away from codimension `2`. -/
def EffectiveCartierDivisorApproximation (D Z : X.IdealSheafData) : Prop :=
  AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ∧
    Z ≤ D ∧ D.agreesAwayFromCodimensionTwo Z

/-- An effective Cartier divisor approximates a closed subscheme exactly when it is contained in
that subscheme and agrees with it away from codimension `2`. -/
theorem effectiveCartierDivisorApproximation_iff (D Z : X.IdealSheafData) :
    EffectiveCartierDivisorApproximation D Z ↔
      AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ∧
        Z ≤ D ∧ D.agreesAwayFromCodimensionTwo Z := sorry

namespace EffectiveCartierDivisorApproximation

/-- A closed subscheme of a Noetherian scheme that is covered by integral effective Cartier
divisors away from codimension `2` admits a finite weighted effective-Cartier approximation. -/
theorem exists_weightedSum
    [IsNoetherian X] (Z : X.IdealSheafData) (D : ι → X.IdealSheafData)
    (hCartier : ∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (D i).subschemeι)
    (hIntegral : ∀ i, IsIntegral (D i).subscheme)
    (Z' : Set X) (hZ'closed : IsClosed Z')
    (hZ'codim : irreducibleComponentsCodimAtLeast 2 Z')
    (hcover : (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X)) :
    ∃ a : ι →₀ ℕ,
      EffectiveCartierDivisorApproximation (effectiveCartierDivisorWeightedSum a D) Z := sorry

/-- A nowhere-dense closed subscheme of a Noetherian scheme whose ambient stalks along its
support are unique factorization monoids is covered by integral effective Cartier divisors away
from a closed subset of codimension at least `2`. -/
theorem exists_cover_of_stalks_uniqueFactorizationMonoid
    [IsNoetherian X] (Z : X.IdealSheafData)
    (hnowhere : IsNowhereDense (Z.support : Set X))
    (hUFD : ∀ x : X, x ∈ Z.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ (ι : Type u) (D : ι → X.IdealSheafData) (Z' : Set X),
      (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (D i).subschemeι) ∧
        (∀ i, IsIntegral (D i).subscheme) ∧
          IsClosed Z' ∧ irreducibleComponentsCodimAtLeast 2 Z' ∧
            (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X) := sorry

/-- A nowhere-dense closed subscheme of a regular Noetherian scheme is covered by integral
effective Cartier divisors away from a closed subset of codimension at least `2`. -/
theorem exists_cover_of_regular
    [IsNoetherian X] [Scheme.Regular X] (Z : X.IdealSheafData)
    (hnowhere : IsNowhereDense (Z.support : Set X)) :
    ∃ (ι : Type u) (D : ι → X.IdealSheafData) (Z' : Set X),
      (∀ i, AlgebraicGeometry.IsEffectiveCartierDivisor (D i).subschemeι) ∧
        (∀ i, IsIntegral (D i).subscheme) ∧
          IsClosed Z' ∧ irreducibleComponentsCodimAtLeast 2 Z' ∧
            (Z.support : Set X) ⊆ Z' ∪ ⋃ i, ((D i).support : Set X) := sorry

/-- A nowhere-dense closed subscheme of a Noetherian scheme has an effective Cartier divisor
approximation when its ambient stalks along the support are unique factorization monoids. -/
theorem exists_of_stalks_uniqueFactorizationMonoid
    [IsNoetherian X] (Z : X.IdealSheafData)
    (hnowhere : IsNowhereDense (Z.support : Set X))
    (hUFD : ∀ x : X, x ∈ Z.support → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D : X.IdealSheafData, EffectiveCartierDivisorApproximation D Z := sorry

/-- A nowhere-dense closed subscheme of a regular Noetherian scheme has an effective Cartier
divisor approximation. -/
theorem exists_of_regular
    [IsNoetherian X] [Scheme.Regular X] (Z : X.IdealSheafData)
    (hnowhere : IsNowhereDense (Z.support : Set X)) :
    ∃ D : X.IdealSheafData, EffectiveCartierDivisorApproximation D Z := sorry

end EffectiveCartierDivisorApproximation

end AlgebraicGeometry.Scheme.IdealSheafData
