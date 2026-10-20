/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinates for bounded finite free complexes

This leaf owns the coordinate-facing operations attached to
`FiniteFreeComplex`: entries of a displayed differential, the rank profile
after deleting two adjacent coordinates, and the canonical head--tail split
of a standard finite free module.  The declarations are independent of the
chapter argument that first uses them, so matrix and basis-change consumers
can import this leaf directly.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

namespace FiniteFreeComplex

variable {e : ℕ}

/-! ### Rank profiles -/

/-- Removing one distinguished coordinate in each of two adjacent degrees. -/
@[stacks 00MS "rank profile after removing adjacent coordinates"]
def splitRank (n : Fin (e + 1) → ℕ) (i : Fin e) : Fin (e + 1) → ℕ :=
  fun j ↦ if j = i.succ ∨ j = i.castSucc then n j - 1 else n j

namespace splitRank

/-- Away from the two removed degrees, `splitRank` agrees with the original rank profile. -/
@[stacks 00MS "unchanged rank away from removed coordinates"]
theorem eq_of_ne_adjacent
    (n : Fin (e + 1) → ℕ) (i : Fin e) {j : Fin (e + 1)}
    (hjSucc : j ≠ i.succ) (hjCast : j ≠ i.castSucc) :
    splitRank n i j = n j := sorry

/-- If the source rank is a successor, deleting its distinguished coordinate gives the predecessor. -/
@[stacks 00MS "source rank after deleting a coordinate"]
theorem succ_eq_of_eq
    (n : Fin (e + 1) → ℕ) (i : Fin e) {ns : ℕ}
    (hsucc : n i.succ = ns + 1) :
    splitRank n i i.succ = ns := sorry

/-- If the target rank is a successor, deleting its distinguished coordinate gives the predecessor. -/
@[stacks 00MS "target rank after deleting a coordinate"]
theorem castSucc_eq_of_eq
    (n : Fin (e + 1) → ℕ) (i : Fin e) {nt : ℕ}
    (hcast : n i.castSucc = nt + 1) :
    splitRank n i i.castSucc = nt := sorry

/-! The rank profile measure decreases whenever a positive source coordinate is removed. -/

/-- Removing one source coordinate from `splitRank` strictly lowers the positive-degree profile
sum when the source rank is positive. -/
@[stacks 00MS "split rank profile decreases"]
theorem positiveRankSumProfile_lt
    (n : Fin (e + 1) → ℕ) (i : Fin e) (hi : 0 < n i.succ) :
    positiveRankSumProfile (splitRank n i) < positiveRankSumProfile n := sorry

end splitRank

section Differential

variable {R : Type u} [Ring R]

/-! ### Differential coordinates -/

/-- The entry of the displayed differential in the chosen standard coordinates. -/
@[stacks 00MS "coordinate entry of a finite free differential"]
def diffEntry (C : _root_.FiniteFreeComplex R e) (i : Fin e)
    (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) : R :=
  C.diffAt i (Pi.single a 1) b

end Differential

section Recoordinate

variable {R : Type u} [Ring R]

/-- A degreewise automorphism of the chosen standard coordinate modules of a finite free
complex. -/
abbrev CoordinateAutomorphism (C : _root_.FiniteFreeComplex R e) :=
  ∀ j : Fin (e + 1), ModuleCat.of R (C.term j) ≅ ModuleCat.of R (C.term j)

/-- Change the chosen coordinates of a finite free complex without changing its underlying chain
complex or rank profile. -/
@[stacks 00MS "degreewise finite-free coordinate change"]
def recoordinate (C : _root_.FiniteFreeComplex R e) (u : C.CoordinateAutomorphism) :
    _root_.FiniteFreeComplex R e where
  toChainComplex := C.toChainComplex
  isZero_toChainComplex_X := C.isZero_toChainComplex_X
  rank := C.rank
  termIso j := C.termIso j ≪≫ u j

namespace recoordinate

/-- Recoordinating preserves the underlying chain complex. -/
@[simp, stacks 00MS "recoordinate underlying complex"]
theorem toChainComplex (C : _root_.FiniteFreeComplex R e) (u : C.CoordinateAutomorphism) :
    (C.recoordinate u).toChainComplex = C.toChainComplex := sorry

/-- Recoordinating preserves the displayed rank profile. -/
@[simp, stacks 00MS "recoordinate rank profile"]
theorem rank (C : _root_.FiniteFreeComplex R e) (u : C.CoordinateAutomorphism) :
    (C.recoordinate u).rank = C.rank := sorry

/-- The coordinate isomorphism after recoordinating is the old one followed by the prescribed
degreewise automorphism. -/
@[simp, stacks 00MS "recoordinate term isomorphism"]
theorem termIso
    (C : _root_.FiniteFreeComplex R e) (u : C.CoordinateAutomorphism) (j : Fin (e + 1)) :
    (C.recoordinate u).termIso j = C.termIso j ≪≫ u j := sorry

/-- A recoordinated displayed differential is conjugated by the source and target coordinate
automorphisms. -/
@[stacks 00MS "recoordinate differential conjugation"]
theorem diffAt
    (C : _root_.FiniteFreeComplex R e) (u : C.CoordinateAutomorphism) (i : Fin e) :
    ModuleCat.ofHom ((C.recoordinate u).diffAt i) =
      (u i.succ).inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ (u i.castSucc).hom := sorry

end recoordinate

end Recoordinate

section HeadTail

variable {R : Type u} [Semiring R]

/-- The standard free module on `Fin (n + 1)` split into tail coordinates and one head coordinate. -/
@[stacks 00MT "head-tail coordinate equivalence"]
noncomputable def headTailEquiv (n : ℕ) :
    (Fin (n + 1) → R) ≃ₗ[R] (Fin n → R) × (Fin 1 → R) :=
  let e₀ : (Fin (n + 1) → R) ≃ₗ[R] (R × (Fin n → R)) :=
    (LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n)) ≪≫ₗ
      LinearEquiv.piOptionEquivProd R
  let e₁ : (R × (Fin n → R)) ≃ₗ[R] ((Fin n → R) × R) :=
    LinearEquiv.prodComm R R (Fin n → R)
  let e₂ : ((Fin n → R) × R) ≃ₗ[R] ((Fin n → R) × (Fin 1 → R)) :=
    LinearEquiv.prodCongr (LinearEquiv.refl R (Fin n → R))
      (LinearEquiv.funUnique (Fin 1) R R).symm
  e₀ ≪≫ₗ e₁ ≪≫ₗ e₂

namespace headTailEquiv

/-- The tail component of the head--tail equivalence consists of the successor coordinates. -/
@[stacks 00MT "tail coordinates of the head-tail equivalence"]
theorem apply_tail (n : ℕ) (x : Fin (n + 1) → R) :
    (headTailEquiv (R := R) n x).1 = fun k ↦ x k.succ := sorry

/-- The head component of the head--tail equivalence is the coordinate at `0`. -/
@[stacks 00MT "head coordinate of the head-tail equivalence"]
theorem apply_head (n : ℕ) (x : Fin (n + 1) → R) :
    (headTailEquiv (R := R) n x).2 = fun _ ↦ x 0 := sorry

/-- Coordinatewise description of the inverse head--tail equivalence. -/
@[stacks 00MT "inverse head-tail coordinate formulas"]
theorem symm_apply_head_tail
    (n : ℕ) (x : Fin n → R) (y : Fin 1 → R) :
    ((headTailEquiv (R := R) n).symm (x, y)) 0 = y 0 ∧
      ∀ k : Fin n, ((headTailEquiv (R := R) n).symm (x, y)) k.succ = x k := sorry

/-- Additive reconstruction formula for the inverse head--tail equivalence. -/
@[stacks 00MT "head-tail basis reconstruction"]
theorem symm_eq_head_tail_sum
    (n : ℕ) (x : Fin n → R) (y : Fin 1 → R) :
    (headTailEquiv (R := R) n).symm (x, y) =
      (Pi.single 0 (y 0) : Fin (n + 1) → R) +
        ∑ k : Fin n, x k • (Pi.single k.succ (1 : R) : Fin (n + 1) → R) := sorry

/-- Permuting coordinates by `Equiv.swap 0 a` evaluates at `0` as evaluation at `a`. -/
@[stacks 00MT "swapped coordinate evaluation"]
theorem piCongrLeft_swap_apply_zero
    {n : ℕ} (a : Fin (n + 1)) (x : Fin (n + 1) → R) :
    (LinearEquiv.piCongrLeft R (fun _ : Fin (n + 1) ↦ R) (Equiv.swap 0 a) x) 0 = x a := sorry

/-- The pure head vector is sent to the distinguished standard basis vector. -/
@[stacks 00MT "pure head basis vector"]
theorem symm_apply_pure_head
    (n : ℕ) :
    (headTailEquiv (R := R) n).symm (0, fun _ ↦ (1 : R)) =
      (Pi.single 0 (1 : R) : Fin (n + 1) → R) := sorry

/-- The inverse head--tail equivalence sends a pure tail basis vector to its successor coordinate. -/
@[stacks 00MT "pure tail basis vector"]
theorem symm_apply_pure_tail
    (n : ℕ) (j : Fin n) :
    (headTailEquiv (R := R) n).symm (Pi.single j (1 : R), 0) =
      (Pi.single j.succ (1 : R) : Fin (n + 1) → R) := sorry

/-- A linear map preserving the head basis vector and killing head coordinates on tail basis vectors
preserves the head coordinate after the head--tail decomposition. -/
@[stacks 00MT "head coordinate under a normalized map"]
theorem map_apply_zero_of_normalized
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hhead : f (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (f ((headTailEquiv (R := R) ns).symm (x, y))) 0 = y 0 := sorry

/-- Under the normalized map hypotheses, the induced map on the head factor is the identity. -/
@[stacks 00MT "normalized head factor"]
theorem apply_head_of_normalized_map
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hhead : f (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (headTailEquiv (R := R) nt
      (f ((headTailEquiv (R := R) ns).symm (x, y)))).2 = y := sorry

/-- Every tail basis vector has zero component in the split-off head factor. -/
@[stacks 00MT "tail basis has zero head component"]
theorem apply_head_of_tail_basis
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0)
    (j : Fin ns) :
    (headTailEquiv (R := R) nt (f (Pi.single j.succ (1 : R)))).2 = 0 := sorry

end headTailEquiv

end HeadTail

section ModuleCat

variable {R : Type u} [Ring R]

/-- The head--tail equivalence viewed as a `ModuleCat` biproduct isomorphism. -/
@[stacks 00MT "head-tail module biproduct equivalence"]
noncomputable def headTailIso (n : ℕ) :
    ModuleCat.of R (Fin (n + 1) → R) ≅
      biprod (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R)) :=
  (headTailEquiv (R := R) n).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R))).symm

namespace headTailIso

/-- The inverse head-tail isomorphism sends a tail vector in the left biproduct summand to the
corresponding tail-plus-zero coordinate vector. -/
@[stacks 00MT "head-tail inverse on the left summand"]
theorem inv_inl_apply (n : ℕ) (x : Fin n → R) :
    ((headTailIso (R := R) n).inv.hom)
        ((biprod.inl :
          ModuleCat.of R (Fin n → R) ⟶
            biprod (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R))).hom x) =
      (headTailEquiv (R := R) n).symm (x, 0) := sorry

/-- The inverse head-tail isomorphism sends a head vector in the right biproduct summand to the
corresponding zero-plus-head coordinate vector. -/
@[stacks 00MT "head-tail inverse on the right summand"]
theorem inv_inr_apply (n : ℕ) (y : Fin 1 → R) :
    ((headTailIso (R := R) n).inv.hom)
        ((biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R))).hom y) =
      (headTailEquiv (R := R) n).symm (0, y) := sorry

/-- Postcomposing the head-tail isomorphism with the first biproduct projection reads the tail
coordinates. -/
@[stacks 00MT "head-tail first projection"]
theorem hom_comp_fst (n : ℕ) :
    (headTailIso (R := R) n).hom ≫ biprod.fst =
      ModuleCat.ofHom
        ((LinearMap.fst R (Fin n → R) (Fin 1 → R)).comp
          (headTailEquiv (R := R) n).toLinearMap) := sorry

/-- Postcomposing the head-tail isomorphism with the second biproduct projection reads the head
coordinate. -/
@[stacks 00MT "head-tail second projection"]
theorem hom_comp_snd (n : ℕ) :
    (headTailIso (R := R) n).hom ≫ biprod.snd =
      ModuleCat.ofHom
        ((LinearMap.snd R (Fin n → R) (Fin 1 → R)).comp
          (headTailEquiv (R := R) n).toLinearMap) := sorry

end headTailIso

end ModuleCat

end FiniteFreeComplex

end
