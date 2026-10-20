/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition
public import ReasLib.NumberTheory.FunctionField.MatrixAdele
public import ReasLib.NumberTheory.Automorphic.CuspForm

/-!
# Finite-level adelic cusp forms for general linear groups
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Matrix
open Finset TopologicalSpace
open scoped RestrictedProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- Right invariance under `GL (Fin n) K`, via `GeneralLinearGroup.map` along
the diagonal embedding `K → A`. -/
def IsRightInvariantGL (n : ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ x γ, f (x * GeneralLinearGroup.map (adeleRing.algebraMap X) γ) = f x

/-- Unfold right `K`-invariance of a `GL (Fin n)`-adelic function. -/
theorem isRightInvariantGL_iff (n : ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsRightInvariantGL X n f ↔
      ∀ x γ, f (x * GeneralLinearGroup.map (adeleRing.algebraMap X) γ) = f x :=
  sorry

/-- Left invariance under integral adelic matrices equal to the identity
outside the open. -/
def IsLeftInvariantOn (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ (u : GL (Fin n) (integerAdeleRing X)),
    (∀ w : closedPoints X.left, w.1 ∉ U → ∀ i j : Fin n,
      u.val i j w = if i = j then 1 else 0) →
    ∀ x, f (GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X) u * x) = f x

/-- Open invariance is simultaneous invariance under the integral adelic
subgroup supported on the open. -/
theorem isLeftInvariantOn_iff (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsLeftInvariantOn X n U f ↔
      ∀ (u : GL (Fin n) (integerAdeleRing X)),
        (∀ w : closedPoints X.left, w.1 ∉ U → ∀ i j : Fin n,
          u.val i j w = if i = j then 1 else 0) →
        ∀ x, f (GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X) u * x) = f x :=
  sorry

/-- The nilpotent part of the unipotent radical of the standard parabolic of
type `c`: strictly block-upper-triangular matrices. -/
def unipotentRadicalNilpotent {R : Type u} [CommRing R] {n : ℕ}
    (c : Composition n) (z : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j ↦ if c.index i < c.index j then z i j else 0

/-- Unfolding of `unipotentRadicalNilpotent` as the displayed block-upper
entries. -/
theorem unipotentRadicalNilpotent_apply {R : Type u} [CommRing R] {n : ℕ}
    (c : Composition n) (z : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    unipotentRadicalNilpotent c z i j =
      if c.index i < c.index j then z i j else 0 := sorry

/-- The unipotent radical of the standard parabolic of type `c`, as a map
`Mₙ(R) → GLₙ(R)`. The inverse is the finite geometric series for a nilpotent
block-upper-triangular matrix. -/
def standardParabolicUnipotent {R : Type u} [CommRing R] {n : ℕ}
    (c : Composition n) (z : Matrix (Fin n) (Fin n) R) : GL (Fin n) R where
  val := 1 + unipotentRadicalNilpotent c z
  inv := ∑ k ∈ Finset.range (n + 1), (-unipotentRadicalNilpotent c z) ^ k
  val_inv := sorry
  inv_val := sorry

/-- The underlying matrix of `standardParabolicUnipotent c z` is `1` plus the
block-upper-triangular nilpotent part. -/
theorem standardParabolicUnipotent_apply {R : Type u} [CommRing R] {n : ℕ}
    (c : Composition n) (z : Matrix (Fin n) (Fin n) R) :
    (standardParabolicUnipotent c z).val =
      1 + unipotentRadicalNilpotent c z := sorry

/-- Index of a strict block-upper coordinate of the unipotent radical of the
standard parabolic of type `c`. -/
structure UnipotentCoordIndex {n : ℕ} (c : Composition n) where
  /-- The row index of the coordinate. -/
  row : Fin n
  /-- The column index of the coordinate. -/
  col : Fin n
  /-- The coordinate is strictly block-upper for `c`. -/
  block_lt : c.index row < c.index col

/-- Package a strictly block-upper pair as a unipotent coordinate index. -/
def UnipotentCoordIndex.of {n : ℕ} (c : Composition n) (row col : Fin n)
    (block_lt : c.index row < c.index col) : UnipotentCoordIndex c :=
  ⟨row, col, block_lt⟩

/-- The packaged pair is strictly block-upper for `c`. -/
theorem UnipotentCoordIndex.spec {n : ℕ} (c : Composition n)
    (p : UnipotentCoordIndex c) : c.index p.row < c.index p.col := sorry

/-- The parameter group of the unipotent radical of type `c`: one copy of the
adele ring for each strict block-upper coordinate. -/
abbrev UnipotentCoords {n : ℕ} (c : Composition n) :=
  UnipotentCoordIndex c → adeleRing X

/-- Addition of unipotent coordinates is pointwise. -/
theorem unipotentCoords_add_apply {n : ℕ} (c : Composition n)
    (z w : UnipotentCoords X c) (p : UnipotentCoordIndex c) :
    (z + w) p = z p + w p := sorry

/-- Principal adeles on the unipotent parameter group of type `c`. -/
def principalUnipotentCoords {n : ℕ} (c : Composition n) :
    AddSubgroup (UnipotentCoords X c) where
  carrier := {z | ∀ p, z p ∈ principalAdeles X}
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry

/-- Membership in `principalUnipotentCoords` is pointwise principality. -/
theorem mem_principalUnipotentCoords {n : ℕ} (c : Composition n)
    (z : UnipotentCoords X c) :
    z ∈ principalUnipotentCoords X c ↔ ∀ p, z p ∈ principalAdeles X := sorry

/-- Realize unipotent coordinates as a matrix supported on strict block-upper
entries. -/
def unipotentCoordMatrix {n : ℕ} (c : Composition n)
    (z : UnipotentCoords X c) : Matrix (Fin n) (Fin n) (adeleRing X) :=
  fun i j ↦
    if h : c.index i < c.index j then z (UnipotentCoordIndex.of c i j h) else 0

/-- Unfolding of `unipotentCoordMatrix` as the displayed block-upper entries. -/
theorem unipotentCoordMatrix_apply {n : ℕ} (c : Composition n)
    (z : UnipotentCoords X c) (i j : Fin n) :
    unipotentCoordMatrix X c z i j =
      if h : c.index i < c.index j then
        z (UnipotentCoordIndex.of c i j h)
      else 0 := sorry

/-- Cuspidality for `GL (Fin n)`: the constant term along the unipotent radical
of every maximal proper standard parabolic is locally constant on the strict
block-upper coordinate group, and has vanishing finite sums over complete
representatives of `N(A) / N(K)`. -/
def IsCuspidalGL (n : ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ (x : GL (Fin n) (adeleRing X)) (c : Composition n),
    c.length = 2 →
      ∃ (U : AddSubgroup (UnipotentCoords X c))
        (s : Finset (UnipotentCoords X c)),
        (∀ z, ∀ u ∈ U,
            f (x * standardParabolicUnipotent c
                (unipotentCoordMatrix X c (z + u))) =
              f (x * standardParabolicUnipotent c
                (unipotentCoordMatrix X c z))) ∧
          IsCompleteReps (principalUnipotentCoords X c ⊔ U) s ∧
            ∑ a ∈ s,
              f (x * standardParabolicUnipotent c
                (unipotentCoordMatrix X c a)) = 0

/-- Unfold `GL (Fin n)` cuspidality into local constancy, complete
representatives, and vanishing sums on strict block-upper coordinates of
maximal proper standard parabolic radicals. -/
theorem isCuspidalGL_iff (n : ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsCuspidalGL X n f ↔
      ∀ (x : GL (Fin n) (adeleRing X)) (c : Composition n),
        c.length = 2 →
          ∃ (U : AddSubgroup (UnipotentCoords X c))
            (s : Finset (UnipotentCoords X c)),
            (∀ z, ∀ u ∈ U,
                f (x * standardParabolicUnipotent c
                    (unipotentCoordMatrix X c (z + u))) =
                  f (x * standardParabolicUnipotent c
                    (unipotentCoordMatrix X c z))) ∧
              IsCompleteReps (principalUnipotentCoords X c ⊔ U) s ∧
                ∑ a ∈ s,
                  f (x * standardParabolicUnipotent c
                    (unipotentCoordMatrix X c a)) = 0 :=
  sorry

/-- `u ∈ GL(O_v)` lies in the principal congruence subgroup of level `m` when
every entry is congruent to the identity modulo `π_v^m`, i.e. has valuation at
most `exp (-m)`. -/
def IsPrincipalCongruence (n : ℕ) (v : closedPoints X.left) (m : ℕ)
    (u : GL (Fin n) (completionIntegers X v)) : Prop :=
  ∀ i j : Fin n,
    Valued.v ((u.val i j : completion X v) - (if i = j then 1 else 0)) ≤
      WithZero.exp (-(m : ℤ))

/-- Unfolding of the principal congruence condition as the displayed valuation
inequalities. -/
theorem isPrincipalCongruence_iff (n : ℕ) (v : closedPoints X.left) (m : ℕ)
    (u : GL (Fin n) (completionIntegers X v)) :
    IsPrincipalCongruence X n v m u ↔
      ∀ i j : Fin n,
        Valued.v ((u.val i j : completion X v) - (if i = j then 1 else 0)) ≤
          WithZero.exp (-(m : ℤ)) := sorry

/-- Simultaneous left invariance under the integral adelic congruence
subgroup with the prescribed exponents outside the open. -/
def IsLeftInvariantLevel (n : ℕ) (U : X.left.Opens)
    (level : closedPoints X.left → ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ (u : GL (Fin n) (integerAdeleRing X)),
    (∀ w : closedPoints X.left, w.1 ∉ U → ∀ i j : Fin n,
      Valued.v ((u.val i j w : completion X w) - (if i = j then 1 else 0)) ≤
        WithZero.exp (-(level w : ℤ))) →
    ∀ x, f (GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X) u * x) = f x

/-- Level invariance is simultaneous invariance under integral adelic
matrices satisfying the local congruence bounds outside the open. -/
theorem isLeftInvariantLevel_iff (n : ℕ) (U : X.left.Opens)
    (level : closedPoints X.left → ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsLeftInvariantLevel X n U level f ↔
      ∀ (u : GL (Fin n) (integerAdeleRing X)),
        (∀ w : closedPoints X.left, w.1 ∉ U → ∀ i j : Fin n,
          Valued.v ((u.val i j w : completion X w) - (if i = j then 1 else 0)) ≤
            WithZero.exp (-(level w : ℤ))) →
        ∀ x, f (GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X) u * x) = f x :=
  sorry

/-- A cuspidal automorphic form for `GL (Fin n)` on `X`, unramified on the open
`U`, of finite level supported on `X \ U`, with values in the coefficient ring
`Λ`. -/
structure CuspFormGL (n : ℕ) (U : X.left.Opens) (Λ : Type v) [CommRing Λ] where
  /-- The underlying function `GL (Fin n) A → Λ`. -/
  toFun : GL (Fin n) (adeleRing X) → Λ
  /-- Right invariance under `GL (Fin n) K`. -/
  right_inv : IsRightInvariantGL X n toFun
  /-- Left invariance under `GL (Fin n) O_v` for closed points `v` of `U`. -/
  left_inv : IsLeftInvariantOn X n U toFun
  /-- Congruence exponents of a compact open level supported on `X \ U`. -/
  level : closedPoints X.left → ℕ
  /-- Left invariance under the principal congruence subgroup of `level` off
  `U`. -/
  level_inv : IsLeftInvariantLevel X n U level toFun
  /-- Vanishing of constant terms along maximal proper standard parabolic radicals. -/
  cuspidal : IsCuspidalGL X n toFun

namespace CuspFormGL

variable {X}
variable {n : ℕ} {U : X.left.Opens} {Λ : Type v} [CommRing Λ]

/-- Build a ramified `GL (Fin n)` cusp form from a function satisfying the
invariance and cuspidality laws, together with a compact open level on `X \ U`. -/
def of (toFun : GL (Fin n) (adeleRing X) → Λ)
    (right_inv : IsRightInvariantGL X n toFun)
    (left_inv : IsLeftInvariantOn X n U toFun)
    (level : closedPoints X.left → ℕ)
    (level_inv : IsLeftInvariantLevel X n U level toFun)
    (cuspidal : IsCuspidalGL X n toFun) : CuspFormGL X n U Λ where
  toFun := toFun
  right_inv := right_inv
  left_inv := left_inv
  level := level
  level_inv := level_inv
  cuspidal := cuspidal

/-- A ramified `GL (Fin n)` cusp form is right `K`-invariant, left `O_v`-invariant
on `U`, of finite level off `U`, and cuspidal along maximal proper parabolics. -/
theorem spec (φ : CuspFormGL X n U Λ) :
    IsRightInvariantGL X n φ.toFun ∧
      IsLeftInvariantOn X n U φ.toFun ∧
        IsLeftInvariantLevel X n U φ.level φ.toFun ∧
          IsCuspidalGL X n φ.toFun := sorry

/-- The compact open level of `CuspFormGL.of` is the supplied exponent
function. -/
theorem of_level (toFun : GL (Fin n) (adeleRing X) → Λ)
    (right_inv : IsRightInvariantGL X n toFun)
    (left_inv : IsLeftInvariantOn X n U toFun)
    (level : closedPoints X.left → ℕ)
    (level_inv : IsLeftInvariantLevel X n U level toFun)
    (cuspidal : IsCuspidalGL X n toFun) :
    (of toFun right_inv left_inv level level_inv cuspidal).level = level :=
  sorry

/-- Ramified `GL (Fin n)` cusp forms are equal if their underlying functions
and levels agree. -/
theorem ext (φ ψ : CuspFormGL X n U Λ) (h : φ.toFun = ψ.toFun)
    (hlevel : φ.level = ψ.level) : φ = ψ := sorry

/-- Pointwise scalar multiplication of ramified `GL (Fin n)` cusp forms,
preserving the compact open level. -/
def smul (a : Λ) (φ : CuspFormGL X n U Λ) : CuspFormGL X n U Λ :=
  of (fun x ↦ a * φ.toFun x) sorry sorry φ.level sorry sorry

/-- The underlying function of `smul a φ` is `a` times `φ.toFun`. -/
theorem smul_toFun (a : Λ) (φ : CuspFormGL X n U Λ) :
    (smul a φ).toFun = fun x ↦ a * φ.toFun x := sorry

/-- Scalar multiplication preserves the compact open level. -/
theorem smul_level (a : Λ) (φ : CuspFormGL X n U Λ) :
    (smul a φ).level = φ.level := sorry

end CuspFormGL

/-- For `GL (Fin 2)`, vanishing of constant terms along proper standard
parabolic radicals agrees with `IsCuspidal`. -/
theorem isCuspidalGL_two_iff {Λ : Type u} [CommRing Λ]
    [Invertible (ringChar k : Λ)]
    (f : GL (Fin 2) (adeleRing X) → Λ) :
    IsCuspidalGL X 2 f ↔ IsCuspidal X f := sorry

/-- An unramified `GL (Fin 2)` cusp form is a `CuspFormGL` on the full open
`⊤`, of trivial level. -/
def UnramifiedCuspForm.toCuspFormGL {Λ : Type u} [CommRing Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] (φ : UnramifiedCuspForm X Λ) :
    CuspFormGL X 2 ⊤ Λ :=
  CuspFormGL.of φ.toFun sorry sorry (fun _ ↦ 0) sorry sorry


end AlgebraicGeometry.SchemeOverField
