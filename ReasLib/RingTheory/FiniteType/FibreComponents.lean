/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Irreducible

/-!
# Explicit finite-type fibre constructions

Finite-type domain maps whose closed fibres realize prescribed irreducible-component
behaviour over polynomial rings.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial MvPolynomial PrimeSpectrum

namespace ProductFibre

/-- The Laurent relation `X 0 * X 1 - 1` presenting `k[x, x⁻¹]`. -/
def relation (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k :=
  X 0 * X 1 - 1

/-- `ProductFibre.relation` is `X 0 * X 1 - 1`. -/
theorem relation_eq (k : Type u) [CommRing k] :
    relation k = X 0 * X 1 - 1 :=
  sorry

/-- The domain `k[x, y] ⧸ (x y - 1)`, a finite-type presentation of `k[x, x⁻¹]`. -/
abbrev UnitRing (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {relation k}

/-- The polynomial ring in `n` variables, used for fibres with exactly `n` components. -/
abbrev ProductRing (k : Type u) [CommRing k] (n : ℕ) : Type u :=
  MvPolynomial (Fin n) k

/-- The product of the indeterminates in `ProductFibre.ProductRing`. -/
def coord (k : Type u) [CommRing k] (n : ℕ) : MvPolynomial (Fin n) k :=
  ∏ i, X i

/-- `ProductFibre.coord k n` is the product of the indeterminates. -/
theorem coord_eq (k : Type u) [CommRing k] (n : ℕ) :
    coord k n = ∏ i, X i :=
  sorry

/-- The `k`-algebra map `k[x] → k[x, x⁻¹]` sending `Polynomial.X` to the class of `X 0`. -/
def algebraMapUnit (k : Type u) [CommRing k] :
    Polynomial k →ₐ[k] UnitRing k :=
  Polynomial.aeval (Ideal.Quotient.mk (Ideal.span {relation k}) (X 0))

/-- `ProductFibre.algebraMapUnit` sends `Polynomial.X` to the class of `X 0`. -/
theorem algebraMapUnit_X (k : Type u) [CommRing k] :
    algebraMapUnit k Polynomial.X =
      Ideal.Quotient.mk (Ideal.span {relation k}) (X 0) :=
  sorry

/-- `ProductFibre.algebraMapUnit` is of finite type. -/
theorem algebraMapUnit_finiteType (k : Type u) [CommRing k] :
    (algebraMapUnit k).FiniteType :=
  sorry

/-- `ProductFibre.algebraMapUnit` is injective. -/
theorem algebraMapUnit_injective (k : Type u) [Field k] :
    Function.Injective (algebraMapUnit k) :=
  sorry

/-- The Laurent presentation `k[x, y] ⧸ (x y - 1)` is a domain. -/
instance instIsDomain_unitRing (k : Type u) [Field k] : IsDomain (UnitRing k) :=
  sorry

/-- The `k`-algebra map `k[x] → k[T_0, …, T_{n-1}]` sending `Polynomial.X` to
`ProductFibre.coord`. -/
def algebraMapProduct (k : Type u) [CommRing k] (n : ℕ) :
    Polynomial k →ₐ[k] ProductRing k n :=
  Polynomial.aeval (coord k n)

/-- `ProductFibre.algebraMapProduct` sends `Polynomial.X` to `ProductFibre.coord`. -/
theorem algebraMapProduct_X (k : Type u) [CommRing k] (n : ℕ) :
    algebraMapProduct k n Polynomial.X = coord k n :=
  sorry

/-- `ProductFibre.algebraMapProduct` is of finite type. -/
theorem algebraMapProduct_finiteType (k : Type u) [CommRing k] (n : ℕ) :
    (algebraMapProduct k n).FiniteType :=
  sorry

/-- For `0 < n`, the product-coordinate map `k[x] → k[T_i]` is injective. -/
theorem algebraMapProduct_injective (k : Type u) [Field k] {n : ℕ} (hn : 0 < n) :
    Function.Injective (algebraMapProduct k n) :=
  sorry

/-- The closed fibre `A / x A` of `ProductFibre.algebraMapUnit`. -/
abbrev closedFibreUnit (k : Type u) [CommRing k] : Type u :=
  UnitRing k ⧸ Ideal.span {algebraMapUnit k Polynomial.X}

/-- The class of the image of `Polynomial.X` vanishes in `ProductFibre.closedFibreUnit`. -/
theorem closedFibreUnit_mk_X (k : Type u) [CommRing k] :
    Ideal.Quotient.mk (Ideal.span {algebraMapUnit k Polynomial.X})
      (algebraMapUnit k Polynomial.X) = 0 :=
  sorry

/-- The closed fibre `A / x A` of `ProductFibre.algebraMapProduct`. -/
abbrev closedFibreProduct (k : Type u) [CommRing k] (n : ℕ) : Type u :=
  ProductRing k n ⧸ Ideal.span {algebraMapProduct k n Polynomial.X}

/-- The class of the image of `Polynomial.X` vanishes in `ProductFibre.closedFibreProduct`. -/
theorem closedFibreProduct_mk_X (k : Type u) [CommRing k] (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {algebraMapProduct k n Polynomial.X})
      (algebraMapProduct k n Polynomial.X) = 0 :=
  sorry

/-- For every `n`, the two explicit finite-type domain maps have zero-fibre
component counts matching the zero and positive cases of `n`. -/
theorem closedFibre_ncard (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    (n = 0 →
      Function.Injective (algebraMapUnit k) ∧
        (algebraMapUnit k).FiniteType ∧
        IsDomain (UnitRing k) ∧
        (irreducibleComponents (PrimeSpectrum (closedFibreUnit k))).encard = (0 : ℕ∞)) ∧
    (0 < n →
      Function.Injective (algebraMapProduct k n) ∧
        (algebraMapProduct k n).FiniteType ∧
        IsDomain (ProductRing k n) ∧
        (irreducibleComponents (PrimeSpectrum (closedFibreProduct k n))).encard =
          (n : ℕ∞)) :=
  sorry

end ProductFibre

namespace AllClosedFibres

/-- The image of `Polynomial.X` in `k[s, t]`: `ST (ST + 1)` in characteristic `2`,
and `(ST) ^ 2` otherwise. -/
def coord (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k :=
  let u := X 0 * X 1
  if ringChar k = 2 then u * (u + 1) else u ^ 2

/-- Unfolding of `AllClosedFibres.coord`. -/
theorem coord_eq (k : Type u) [CommRing k] :
    coord k =
      let u := X 0 * X 1
      if ringChar k = 2 then u * (u + 1) else u ^ 2 :=
  sorry

/-- The domain `k[s, t]` of the universally reducible-fibre construction. -/
abbrev Ring (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (Fin 2) k

/-- The `k[x]`-algebra map sending `Polynomial.X` to `AllClosedFibres.coord`. -/
def algebraMap (k : Type u) [CommRing k] : Polynomial k →ₐ[k] Ring k :=
  Polynomial.aeval (coord k)

/-- `AllClosedFibres.algebraMap` sends `Polynomial.X` to `AllClosedFibres.coord`. -/
theorem algebraMap_X (k : Type u) [CommRing k] :
    algebraMap k Polynomial.X = coord k :=
  sorry

/-- `AllClosedFibres.algebraMap` is of finite type. -/
theorem algebraMap_finiteType (k : Type u) [CommRing k] :
    (algebraMap k).FiniteType :=
  sorry

/-- `AllClosedFibres.algebraMap` is injective. -/
theorem algebraMap_injective (k : Type u) [Field k] :
    Function.Injective (algebraMap k) :=
  sorry

/-- The closed fibre `A / (x - α) A` of `AllClosedFibres.algebraMap`. -/
abbrev closedFibre (k : Type u) [CommRing k] (α : k) : Type u :=
  Ring k ⧸ Ideal.span {algebraMap k (Polynomial.X - Polynomial.C α)}

/-- The class of `Polynomial.X - Polynomial.C α` vanishes in the closed fibre. -/
theorem closedFibre_mk_X_sub_C (k : Type u) [CommRing k] (α : k) :
    Ideal.Quotient.mk (Ideal.span {algebraMap k (Polynomial.X - Polynomial.C α)})
      (algebraMap k (Polynomial.X - Polynomial.C α)) = 0 :=
  sorry

/-- Every scalar closed fibre is nonempty and not irreducible. -/
theorem closedFibre_reducible (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Injective (algebraMap k) ∧
      (algebraMap k).FiniteType ∧
      IsDomain (Ring k) ∧
      ∀ α : k, Nonempty (PrimeSpectrum (closedFibre k α)) ∧
        ¬ IrreducibleSpace (PrimeSpectrum (closedFibre k α)) :=
  sorry

end AllClosedFibres

namespace OriginFibre

/-- The domain `k[u, v, w]` of the exceptional-origin construction. -/
abbrev Ring (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (Fin 3) k

/-- The map `k[x, y] → k[u, v, w]` sending `(x, y)` to `(u v, u w)`. -/
def algebraMap (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →ₐ[k] Ring k :=
  MvPolynomial.aeval fun i : Fin 2 ↦
    if i = 0 then X (0 : Fin 3) * X 1 else X (0 : Fin 3) * X 2

/-- `OriginFibre.algebraMap` sends `X 0` to `X 0 * X 1`. -/
theorem algebraMap_X0 (k : Type u) [CommRing k] :
    algebraMap k (X 0) = X (0 : Fin 3) * X 1 :=
  sorry

/-- `OriginFibre.algebraMap` sends `X 1` to `X 0 * X 2`. -/
theorem algebraMap_X1 (k : Type u) [CommRing k] :
    algebraMap k (X 1) = X (0 : Fin 3) * X 2 :=
  sorry

/-- `OriginFibre.algebraMap` is of finite type. -/
theorem algebraMap_finiteType (k : Type u) [CommRing k] :
    (algebraMap k).FiniteType :=
  sorry

/-- `OriginFibre.algebraMap` is injective. -/
theorem algebraMap_injective (k : Type u) [Field k] :
    Function.Injective (algebraMap k) :=
  sorry

/-- The closed fibre `A / (x - α, y - β) A` of `OriginFibre.algebraMap`. -/
abbrev closedFibre (k : Type u) [CommRing k] (α β : k) : Type u :=
  Ring k ⧸
    Ideal.span
      {algebraMap k (X 0 - MvPolynomial.C α), algebraMap k (X 1 - MvPolynomial.C β)}

/-- The image of `X 0 - C α` vanishes in the closed fibre. -/
theorem closedFibre_mk_X0_sub_C (k : Type u) [CommRing k] (α β : k) :
    Ideal.Quotient.mk
        (Ideal.span
          {algebraMap k (X 0 - MvPolynomial.C α),
            algebraMap k (X 1 - MvPolynomial.C β)})
        (algebraMap k (X 0 - MvPolynomial.C α)) =
      0 :=
  sorry

/-- The image of `X 1 - C β` vanishes in the closed fibre. -/
theorem closedFibre_mk_X1_sub_C (k : Type u) [CommRing k] (α β : k) :
    Ideal.Quotient.mk
        (Ideal.span
          {algebraMap k (X 0 - MvPolynomial.C α),
            algebraMap k (X 1 - MvPolynomial.C β)})
        (algebraMap k (X 1 - MvPolynomial.C β)) =
      0 :=
  sorry

/-- Fibres away from the origin are irreducible, while the origin fibre is
nonempty and not irreducible. -/
theorem closedFibre_irreducible_of_ne_zero (k : Type u) [Field k] [IsAlgClosed k] :
    Function.Injective (algebraMap k) ∧
      (algebraMap k).FiniteType ∧
      IsDomain (Ring k) ∧
      (∀ α β : k, (α, β) ≠ (0, 0) →
        IrreducibleSpace (PrimeSpectrum (closedFibre k α β))) ∧
      Nonempty (PrimeSpectrum (closedFibre k 0 0)) ∧
      ¬ IrreducibleSpace (PrimeSpectrum (closedFibre k 0 0)) :=
  sorry

end OriginFibre
