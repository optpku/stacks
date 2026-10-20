/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.RingTheory.PowerSeries.Trunc

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

/-- A total-Chern-class theory for the finite locally free modules on a scheme, with
chosen total series and top coefficients satisfying normalization and a splitting principle. -/
structure ExteriorPowerChernClassTheory
    (X : _root_.AlgebraicGeometry.Scheme.{u}) (A : Type v) [CommRing A] where
  /-- The unit-valued total Chern series of a finite locally free module of known rank. -/
  totalChern (F : X.Modules) (q : ℕ) [F.IsFiniteLocallyFreeOfRank q] :
    (PowerSeries A)ˣ
  /-- The top Chern coefficient of a finite locally free module of known rank. -/
  topChern (F : X.Modules) (q : ℕ) [F.IsFiniteLocallyFreeOfRank q] : A
  /-- The constant coefficient of every total Chern series is one. -/
  coeff_zero (F : X.Modules) (q : ℕ) [F.IsFiniteLocallyFreeOfRank q] :
    PowerSeries.coeff 0 (totalChern F q : PowerSeries A) = 1
  /-- The coefficient in the rank equals the chosen top Chern coefficient. -/
  coeff_top (F : X.Modules) (q : ℕ) [F.IsFiniteLocallyFreeOfRank q] :
    PowerSeries.coeff q (totalChern F q : PowerSeries A) = topChern F q
  /-- Every total Chern series and those of its exterior powers become the elementary
  root products after an injective extension of coefficient rings. -/
  splitting_principle (E : X.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] :
    ∃ (B : Type v) (_ : CommRing B) (ι : A →+* B), Function.Injective ι ∧
      ∃ roots : Fin r → B,
        PowerSeries.map ι (totalChern E r : PowerSeries A) =
            ∏ i : Fin r, (1 + PowerSeries.C (roots i) * PowerSeries.X) ∧
          ∀ n : Fin (r + 1),
            PowerSeries.map ι
                (totalChern (Λ[(n : ℕ)] E) (Nat.choose r n) : PowerSeries A) =
              ∏ I ∈ (Finset.univ : Finset (Fin r)).powersetCard n,
                (1 + PowerSeries.C (∑ i ∈ I, roots i) * PowerSeries.X)

/-- The total Chern series has constant coefficient one, and its coefficient in the
rank is the chosen top Chern coefficient. -/
theorem ExteriorPowerChernClassTheory.coeff_spec
    {X : _root_.AlgebraicGeometry.Scheme.{u}} {A : Type v} [CommRing A]
    (theory : ExteriorPowerChernClassTheory X A)
    (F : X.Modules) (q : ℕ) [F.IsFiniteLocallyFreeOfRank q] :
    PowerSeries.coeff 0 (theory.totalChern F q : PowerSeries A) = 1 ∧
      PowerSeries.coeff q (theory.totalChern F q : PowerSeries A) =
        theory.topChern F q := sorry

/-- The alternating product of the total Chern series of all exterior powers of a
finite locally free module. -/
noncomputable def alternatingChernProduct
    {X : _root_.AlgebraicGeometry.Scheme.{u}} {A : Type v} [CommRing A]
    (theory : ExteriorPowerChernClassTheory X A)
    (E : X.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] :
    (PowerSeries A)ˣ :=
  ∏ n : Fin (r + 1),
    theory.totalChern (Λ[(n : ℕ)] E) (Nat.choose r n) ^ ((-1 : ℤ) ^ (n : ℕ))

/-- The underlying power series of `alternatingChernProduct` is the corresponding product
of the underlying powers of the total Chern units. -/
theorem alternatingChernProduct_coe
    {X : _root_.AlgebraicGeometry.Scheme.{u}} {A : Type v} [CommRing A]
    (theory : ExteriorPowerChernClassTheory X A)
    (E : X.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] :
    (alternatingChernProduct theory E r : PowerSeries A) =
      (∏ n : Fin (r + 1),
        theory.totalChern (Λ[(n : ℕ)] E) (Nat.choose r n) ^ ((-1 : ℤ) ^ (n : ℕ)) :
          (PowerSeries A)ˣ) := sorry

/-- For a positive-rank finite locally free module whose Chern classes split into roots,
the alternating product of the total Chern series of its exterior powers is one below the
rank, with degree-`r` term the negative of `(r - 1)!` times the top Chern coefficient. -/
theorem alternatingChernProduct_trunc_of_roots
    {X : _root_.AlgebraicGeometry.Scheme.{u}} {A : Type v} [CommRing A]
    (theory : ExteriorPowerChernClassTheory X A)
    (E : X.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] (hr : 0 < r)
    {B : Type w} [CommRing B] (ι : A →+* B) (hι : Function.Injective ι)
    (roots : Fin r → B)
    (hE : PowerSeries.map ι (theory.totalChern E r : PowerSeries A) =
      ∏ i : Fin r, (1 + PowerSeries.C (roots i) * PowerSeries.X))
    (hExterior : ∀ n : Fin (r + 1),
      PowerSeries.map ι
          (theory.totalChern (Λ[(n : ℕ)] E) (Nat.choose r n) : PowerSeries A) =
        ∏ I ∈ (Finset.univ : Finset (Fin r)).powersetCard n,
          (1 + PowerSeries.C (∑ i ∈ I, roots i) * PowerSeries.X)) :
    PowerSeries.trunc (r + 1)
        (alternatingChernProduct theory E r : PowerSeries A) =
      1 - Polynomial.monomial r
        (((r - 1).factorial : A) *
          PowerSeries.coeff r (theory.totalChern E r : PowerSeries A)) := sorry

/-- For a positive-rank finite locally free module, the alternating product of the total
Chern series of its exterior powers is one below the rank, and its rank coefficient is the
negative of `(r - 1)!` times the top Chern coefficient. -/
theorem alternatingChernProduct_trunc
    {X : _root_.AlgebraicGeometry.Scheme.{u}} {A : Type v} [CommRing A]
    (theory : ExteriorPowerChernClassTheory X A)
    (E : X.Modules) (r : ℕ) [E.IsFiniteLocallyFreeOfRank r] (hr : 0 < r) :
    PowerSeries.trunc (r + 1)
        (alternatingChernProduct theory E r : PowerSeries A) =
      1 - Polynomial.monomial r
        (((r - 1).factorial : A) * theory.topChern E r) := sorry

end AlgebraicGeometry.Scheme.Modules
