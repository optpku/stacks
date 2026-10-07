module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Instances.Matrix
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import stacks_project.Chap64.Definition_64_31_1_Adele
public import stacks_project.Chap64.Definition_64_31_1_CuspForm
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius
public import stacks_project.Chap64.Theorem_64_31_2_Hecke

/-!
# Ramified GLₙ cusp forms and Satake eigenvalues

This leaf owns the open restriction of a scheme over a field, the embeddings
of `GL (Fin n) K` and `GL (Fin n) O_v` into `GL (Fin n) A`, ramified
`GL (Fin n)` cusp forms unramified on a nonempty open and of finite level
on `X \ U`, spherical Hecke operators `T_{v,i}` as sums over invertible
Grassmannian-frame representatives, and the Satake eigenvalue package of an
eigenform.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Matrix
open Finset TopologicalSpace
open scoped RestrictedProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The open `U` of `X`, viewed as a scheme over `k` via `U.ι ≫ X.hom`. -/
def openRestrict (X : SchemeOverField k) (U : X.left.Opens) : SchemeOverField k :=
  Over.mk (U.ι ≫ X.hom)

/-- The underlying scheme of `openRestrict X U` is `U.toScheme`. -/
theorem openRestrict_left (X : SchemeOverField k) (U : X.left.Opens) :
    (openRestrict X U).left = U.toScheme := sorry

/-- The structure map of `openRestrict X U` is locally of finite type as soon as
`X.hom` is. -/
instance locallyOfFiniteType_openRestrict (X : SchemeOverField k) (U : X.left.Opens)
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (openRestrict X U).hom :=
  locallyOfFiniteType_comp U.ι X.hom

/-- The image of a closed point of `U` in `X`. -/
def closedPointEmbed (X : SchemeOverField k) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) : closedPoints X.left :=
  ⟨U.ι.base v.1, sorry⟩

/-- The image of `closedPointEmbed` lies in the open `U`. -/
theorem closedPointEmbed_mem (X : SchemeOverField k) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) :
    (closedPointEmbed X U v).1 ∈ U := sorry

variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- The elementary unipotent `I + z E_ij` in `GL (Fin n) R`. -/
def elementaryUnipotent {R : Type u} [CommRing R] {n : ℕ} (i j : Fin n) (z : R) :
    GL (Fin n) R where
  val := 1 + Matrix.single i j z
  inv := 1 + Matrix.single i j (-z)
  val_inv := sorry
  inv_val := sorry

/-- The underlying matrix of `elementaryUnipotent i j z` is `1 + single i j z`. -/
theorem elementaryUnipotent_apply {R : Type u} [CommRing R] {n : ℕ}
    (i j : Fin n) (z : R) :
    (elementaryUnipotent i j z).val = 1 + Matrix.single i j z := sorry

/-- Extend a matrix over `O_v` by the identity at every other place. -/
def extendLocalIntegerMatrix (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (completionIntegers X v)) :
    Matrix (Fin n) (Fin n) (integerAdeleRing X) :=
  fun i j w =>
    match Classical.decEq (closedPoints X.left) w v with
    | isTrue h => h.symm ▸ m i j
    | isFalse _ => if i = j then 1 else 0

/-- The `v`-component of `extendLocalIntegerMatrix n X v m` is `m`. -/
theorem extendLocalIntegerMatrix_apply_self (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (completionIntegers X v)) (i j : Fin n) :
    extendLocalIntegerMatrix X n v m i j v = m i j := sorry

/-- Off `v`, `extendLocalIntegerMatrix` is the identity matrix. -/
theorem extendLocalIntegerMatrix_apply_of_ne (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (completionIntegers X v))
    (w : closedPoints X.left) (hw : w ≠ v) (i j : Fin n) :
    extendLocalIntegerMatrix X n v m i j w = if i = j then 1 else 0 := sorry

/-- The group embedding `GL (Fin n) O_v →* GL (Fin n) O` placing a local
integral matrix at `v` and the identity elsewhere. -/
def extendLocalIntegerGL (n : ℕ) (v : closedPoints X.left) :
    GL (Fin n) (completionIntegers X v) →* GL (Fin n) (integerAdeleRing X) where
  toFun u :=
    { val := extendLocalIntegerMatrix X n v u.val
      inv := extendLocalIntegerMatrix X n v u.inv
      val_inv := sorry
      inv_val := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- `extendLocalIntegerGL` acts by `extendLocalIntegerMatrix` on the underlying
matrices. -/
theorem extendLocalIntegerGL_apply (n : ℕ) (v : closedPoints X.left)
    (u : GL (Fin n) (completionIntegers X v)) :
    (extendLocalIntegerGL X n v u).val = extendLocalIntegerMatrix X n v u.val :=
  sorry

/-- The embedding `GL (Fin n) O_v →* GL (Fin n) A` obtained by extending to
integral adeles and applying `GeneralLinearGroup.map` along `O → A`. -/
def localIntegerGL (n : ℕ) (v : closedPoints X.left) :
    GL (Fin n) (completionIntegers X v) →* GL (Fin n) (adeleRing X) :=
  (GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X)).comp
    (extendLocalIntegerGL X n v)

/-- `localIntegerGL` is `GeneralLinearGroup.map` of the local integral extension
along `O → A`. -/
theorem localIntegerGL_apply (n : ℕ) (v : closedPoints X.left)
    (u : GL (Fin n) (completionIntegers X v)) :
    localIntegerGL X n v u =
      GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X)
        (extendLocalIntegerGL X n v u) := sorry

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

/-- Left invariance under `GL (Fin n) O_v` at closed points of `U` only. -/
def IsLeftInvariantOn (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ (v : closedPoints X.left), v.1 ∈ U →
    ∀ (u : GL (Fin n) (completionIntegers X v)) x,
      f (localIntegerGL X n v u * x) = f x

/-- Unfold left `O_v`-invariance on the unramified open `U`. -/
theorem isLeftInvariantOn_iff (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsLeftInvariantOn X n U f ↔
      ∀ (v : closedPoints X.left), v.1 ∈ U →
        ∀ (u : GL (Fin n) (completionIntegers X v)) x,
          f (localIntegerGL X n v u * x) = f x := sorry

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
of every proper standard parabolic is locally constant on the strict
block-upper coordinate group, and has vanishing finite sums over complete
representatives of `N(A) / N(K)`. -/
def IsCuspidalGL (n : ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ (x : GL (Fin n) (adeleRing X)) (c : Composition n),
    1 < c.length →
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
proper standard parabolic radicals. -/
theorem isCuspidalGL_iff (n : ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsCuspidalGL X n f ↔
      ∀ (x : GL (Fin n) (adeleRing X)) (c : Composition n),
        1 < c.length →
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

/-- Left invariance under the principal congruence subgroup of exponent
`level v` at every closed point outside `U`. -/
def IsLeftInvariantLevel (n : ℕ) (U : X.left.Opens)
    (level : closedPoints X.left → ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) : Prop :=
  ∀ (v : closedPoints X.left), v.1 ∉ U →
    ∀ (u : GL (Fin n) (completionIntegers X v)),
      IsPrincipalCongruence X n v (level v) u →
        ∀ x, f (localIntegerGL X n v u * x) = f x

/-- Unfold left congruence-level invariance off `U`. -/
theorem isLeftInvariantLevel_iff (n : ℕ) (U : X.left.Opens)
    (level : closedPoints X.left → ℕ) {Λ : Type v} [CommRing Λ]
    (f : GL (Fin n) (adeleRing X) → Λ) :
    IsLeftInvariantLevel X n U level f ↔
      ∀ (v : closedPoints X.left), v.1 ∉ U →
        ∀ (u : GL (Fin n) (completionIntegers X v)),
          IsPrincipalCongruence X n v (level v) u →
            ∀ x, f (localIntegerGL X n v u * x) = f x := sorry

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
  /-- Vanishing of constant terms along proper standard parabolic radicals. -/
  cuspidal : IsCuspidalGL X n toFun

namespace CuspFormGL

variable {X}
variable {n : ℕ} {U : X.left.Opens} {Λ : Type v} [CommRing Λ]

/-- Build a ramified `GL (Fin n)` cusp form from a function satisfying the
source laws, together with a compact open level on `X \ U`. -/
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
on `U`, of finite level off `U`, and cuspidal along proper parabolics. -/
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

/-- Pointwise scalar multiplication of ramified `GL (Fin n)` cusp forms. -/
instance instSMul : SMul Λ (CuspFormGL X n U Λ) where
  smul := smul

/-- The underlying function of `a • φ` is `a` times `φ.toFun`. -/
theorem smul_toFun (a : Λ) (φ : CuspFormGL X n U Λ) :
    (a • φ).toFun = fun x ↦ a * φ.toFun x := sorry

/-- Scalar multiplication preserves the compact open level. -/
theorem smul_level (a : Λ) (φ : CuspFormGL X n U Λ) :
    (a • φ).level = φ.level := sorry

end CuspFormGL

/-- Embed a local matrix at the place `v`, as the identity at every other place. -/
def embedLocalMatrix (n : ℕ) (v : closedPoints X.left)
    (M : Matrix (Fin n) (Fin n) (completion X v)) :
    Matrix (Fin n) (Fin n) (adeleRing X) :=
  open Classical in
    fun i j ↦
      if i = j then
        RestrictedProduct.mulSingle (fun w ↦ completionIntegers X w) v (M i j)
      else RestrictedProduct.single (fun w ↦ completionIntegers X w) v (M i j)

/-- The `v`-component of `embedLocalMatrix` is the original local matrix. -/
theorem embedLocalMatrix_apply (n : ℕ) (v : closedPoints X.left)
    (M : Matrix (Fin n) (Fin n) (completion X v)) (i j : Fin n) :
    embedLocalMatrix X n v M i j v = M i j :=
  sorry

/-- Embed `GL (Fin n) K_v` into `GL (Fin n) A` by the identity at every other
place. -/
def embedLocalGL (n : ℕ) (v : closedPoints X.left)
    (g : GL (Fin n) (completion X v)) : GL (Fin n) (adeleRing X) where
  val := embedLocalMatrix X n v g.val
  inv := embedLocalMatrix X n v g.inv
  val_inv := sorry
  inv_val := sorry

/-- The underlying matrix of `embedLocalGL` is `embedLocalMatrix` of the local
matrix. -/
theorem embedLocalGL_val (n : ℕ) (v : closedPoints X.left)
    (g : GL (Fin n) (completion X v)) :
    (embedLocalGL X n v g).val = embedLocalMatrix X n v g.val := sorry

/-- The diagonal matrix `diag(π^{-1}, …, π^{-1}, 1, …, 1)` in `GL (Fin n) K_v`
with `i` copies of `π^{-1}`. -/
def satakeLocalDiag (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) : GL (Fin n) (completion X v) where
  val := Matrix.diagonal fun j ↦ if j.val < i then π.inv else 1
  inv := Matrix.diagonal fun j ↦ if j.val < i then π.val else 1
  val_inv := sorry
  inv_val := sorry

/-- Unfolding of `satakeLocalDiag` as the displayed diagonal matrix. -/
theorem satakeLocalDiag_spec (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) :
    (satakeLocalDiag X n v i π).val =
      Matrix.diagonal fun j ↦ if j.val < i then π.inv else 1 := sorry

/-- The spherical diagonal element `diag(π^{-1}^i, 1^{n-i})` embedded in
`GL (Fin n) A`. -/
def satakeDiag (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) : GL (Fin n) (adeleRing X) :=
  embedLocalGL X n v (satakeLocalDiag X n v i π)

/-- `satakeDiag` is the local embedding of `satakeLocalDiag`. -/
theorem satakeDiag_spec (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (π : (completion X v)ˣ) :
    satakeDiag X n v i π =
      embedLocalGL X n v (satakeLocalDiag X n v i π) := sorry

/-- The Grassmannian of `i`-planes in `κ(v)^n`, indexing left `GL(O_v)`-cosets
in the spherical double coset of `diag(π^{-1}^i, 1^{n-i})`. -/
structure HeckeCosetIndex (n : ℕ) (v : closedPoints X.left) (i : ℕ) where
  /-- The underlying `i`-plane in `κ(v)^n`. -/
  carrier : Submodule (X.left.residueField v.1)
    (Fin n → X.left.residueField v.1)
  /-- The packaged subspace has finite rank `i`. -/
  finrank_eq : Module.finrank (X.left.residueField v.1) carrier = i

/-- Package an `i`-plane in `κ(v)^n` as a spherical Hecke-coset index. -/
def HeckeCosetIndex.of (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (carrier : Submodule (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1))
    (finrank_eq : Module.finrank (X.left.residueField v.1) carrier = i) :
    HeckeCosetIndex X n v i :=
  ⟨carrier, finrank_eq⟩

/-- The carrier of `HeckeCosetIndex.of` is the given subspace. -/
theorem HeckeCosetIndex.of_carrier (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (carrier : Submodule (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1))
    (finrank_eq : Module.finrank (X.left.residueField v.1) carrier = i) :
    (HeckeCosetIndex.of X n v carrier finrank_eq).carrier = carrier := sorry

/-- The packaged plane has finite rank `i`. -/
theorem HeckeCosetIndex.spec (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.finrank (X.left.residueField v.1) W.carrier = i := sorry

/-- Submodules of a finite vector space over a finite residue field are finite. -/
instance instFinite_submodule (n : ℕ) (v : closedPoints X.left)
    [Finite (X.left.residueField v.1)] :
    Finite
      (Submodule (X.left.residueField v.1)
        (Fin n → X.left.residueField v.1)) :=
  Finite.of_injective
    (SetLike.coe :
      Submodule (X.left.residueField v.1) (Fin n → X.left.residueField v.1) →
        Set (Fin n → X.left.residueField v.1))
    SetLike.coe_injective

/-- The Grassmannian `HeckeCosetIndex` is finite. -/
instance instFinite_heckeCosetIndex (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    [Finite (X.left.residueField v.1)] :
    Finite (HeckeCosetIndex X n v i) :=
  Finite.of_equiv
    { W : Submodule (X.left.residueField v.1)
        (Fin n → X.left.residueField v.1) //
      Module.finrank (X.left.residueField v.1) W = i }
    { toFun := fun W ↦ HeckeCosetIndex.of X n v W.1 W.2
      invFun := fun W ↦ ⟨W.carrier, W.finrank_eq⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- A `Fintype` instance on the spherical double-coset index. -/
noncomputable instance instFintype_heckeCosetIndex (n : ℕ)
    (v : closedPoints X.left) (i : ℕ) [Finite (X.left.residueField v.1)] :
    Fintype (HeckeCosetIndex X n v i) :=
  Fintype.ofFinite _

/-- Complementary subspace to an `i`-plane in `κ(v)^n`. -/
def grassmannianComplement (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Submodule (X.left.residueField v.1) (Fin n → X.left.residueField v.1) :=
  LinearMap.ker W.carrier.subtype.leftInverse

/-- `grassmannianComplement` is complementary to `W`. -/
theorem grassmannianComplement_isCompl (n : ℕ) (v : closedPoints X.left)
    {i : ℕ} (W : HeckeCosetIndex X n v i) :
    IsCompl W.carrier (grassmannianComplement X n v W) := sorry

/-- A basis of the `i`-plane `W`. -/
def grassmannianWBasis (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.Basis (Fin i) (X.left.residueField v.1) W.carrier :=
  Module.finBasisOfFinrankEq (X.left.residueField v.1) W.carrier W.finrank_eq

/-- A basis of the complementary subspace to `W`. -/
def grassmannianComplBasis (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.Basis (Fin (n - i)) (X.left.residueField v.1)
      (grassmannianComplement X n v W) :=
  let hsum :=
    Submodule.finrank_add_eq_of_isCompl
      (LinearMap.isCompl_of_proj
        (LinearMap.leftInverse_apply_of_inj W.carrier.ker_subtype))
  Module.finBasisOfFinrankEq (X.left.residueField v.1)
    (grassmannianComplement X n v W)
    (Nat.eq_sub_of_add_eq
      ((Nat.add_comm
          (Module.finrank (X.left.residueField v.1)
            (grassmannianComplement X n v W))
          i).trans
        (((Eq.symm
              (congrArg
                (fun m : ℕ ↦
                  Nat.add m
                    (Module.finrank (X.left.residueField v.1)
                      (grassmannianComplement X n v W)))
                W.finrank_eq)).trans hsum).trans
          (Module.finrank_fin_fun (X.left.residueField v.1)))))

/-- A basis of `κ(v)^n` whose first `i` vectors span `W` and whose remaining
vectors span a complementary subspace. -/
def grassmannianFrameBasis (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Module.Basis (Fin i ⊕ Fin (n - i)) (X.left.residueField v.1)
      (Fin n → X.left.residueField v.1) :=
  ((grassmannianWBasis X n v W).prod (grassmannianComplBasis X n v W)).map
    (Submodule.prodEquivOfIsCompl W.carrier (grassmannianComplement X n v W)
      (LinearMap.isCompl_of_proj
        (LinearMap.leftInverse_apply_of_inj W.carrier.ker_subtype)))

/-- Residue-level frame in `GL (Fin n, κ(v))` whose first `i` columns are a
basis of `W` and whose remaining columns complete it to a basis of `κ(v)^n`. -/
def grassmannianResidueMatrix (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    Matrix (Fin n) (Fin n) (X.left.residueField v.1) :=
  fun row col ↦
    if h : i ≤ n then
      ((grassmannianFrameBasis X n v W).reindex
          (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))) col :
        Fin n → X.left.residueField v.1) row
    else if row = col then 1 else 0

/-- The residue-level general linear frame of an `i`-plane, with inverse the
adjugate scaled by the inverse determinant. -/
def grassmannianResidueGL (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    GL (Fin n) (X.left.residueField v.1) where
  val := grassmannianResidueMatrix X n v W
  inv :=
    (grassmannianResidueMatrix X n v W).det⁻¹ •
      (grassmannianResidueMatrix X n v W).adjugate
  val_inv := sorry
  inv_val := sorry

/-- The residue determinant of a Grassmannian frame is a unit. -/
theorem grassmannianResidueGL_isUnit (n : ℕ) (v : closedPoints X.left)
    {i : ℕ} (W : HeckeCosetIndex X n v i) :
    IsUnit (grassmannianResidueMatrix X n v W).det := sorry

/-- Lift a residue matrix to a matrix over `O_v`. -/
def liftResidueMatrix (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (X.left.residueField v.1)) :
    Matrix (Fin n) (Fin n) (completionIntegers X v) :=
  fun a b ↦
    algebraMap (X.left.presheaf.stalk v.1) (completionIntegers X v)
      (Quotient.out (m a b))

/-- The `O_v`-lift of a residue matrix coerces to `residueRep` entrywise. -/
theorem liftResidueMatrix_apply (n : ℕ) (v : closedPoints X.left)
    (m : Matrix (Fin n) (Fin n) (X.left.residueField v.1)) (a b : Fin n) :
    (liftResidueMatrix X n v m a b : completion X v) =
      residueRep X v (m a b) := sorry

/-- The determinant of the lifted frame is a unit of `O_v`, since its reduction
is the determinant of a basis matrix over `κ(v)`. -/
theorem grassmannianLocalDet_isUnit (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    IsUnit (liftResidueMatrix X n v (grassmannianResidueGL X n v W).val).det := sorry

/-- The integral lift of a Grassmannian frame. Its inverse is computed over
`O_v` itself as the adjugate times the inverse of the unit determinant. -/
def grassmannianLocalGL (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) :
    GL (Fin n) (completionIntegers X v) where
  val := liftResidueMatrix X n v (grassmannianResidueGL X n v W).val
  inv :=
    Ring.inverse (liftResidueMatrix X n v (grassmannianResidueGL X n v W).val).det •
      (liftResidueMatrix X n v (grassmannianResidueGL X n v W).val).adjugate
  val_inv := sorry
  inv_val := sorry

/-- The image of `grassmannianLocalGL` in `GL (Fin n) K_v`. -/
def grassmannianCompletionGL (n : ℕ) (v : closedPoints X.left) {i : ℕ}
    (W : HeckeCosetIndex X n v i) : GL (Fin n) (completion X v) :=
  GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v))
    (grassmannianLocalGL X n v W)

/-- `grassmannianCompletionGL` is `GeneralLinearGroup.map` of the integral
frame along `O_v → K_v`. -/
theorem grassmannianCompletionGL_spec (n : ℕ) (v : closedPoints X.left)
    {i : ℕ} (W : HeckeCosetIndex X n v i) :
    grassmannianCompletionGL X n v W =
      GeneralLinearGroup.map
        (ValuationSubring.subtype (completionIntegers X v))
        (grassmannianLocalGL X n v W) := sorry

/-- From a column frame `g`, form `D * gᵀ`, so the first `i` rows before
scaling span the plane carried by the first `i` columns of `g`. The written
inverse is `(g⁻¹)ᵀ * D⁻¹`. This orientation parametrizes left integral cosets. -/
def heckeLeftRepresentative {R : Type u} [CommRing R] (n i : ℕ)
    (π : Rˣ) (g : GL (Fin n) R) : GL (Fin n) R where
  val := (Matrix.diagonal fun j : Fin n ↦ if j.val < i then π.inv else 1) * g.val.transpose
  inv := g.inv.transpose * (Matrix.diagonal fun j : Fin n ↦ if j.val < i then π.val else 1)
  val_inv := sorry
  inv_val := sorry

/-- The local left-coset representative attached to `W`. Transposing the lifted
column frame makes its first `i` rows span `W`; left multiplication by the
diagonal scales exactly these rows. In degree `n`, use the scalar itself. -/
def heckeLocalCosetRep (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W : HeckeCosetIndex X n v i) (π : (completion X v)ˣ) :
    GL (Fin n) (completion X v) :=
  if i = n then satakeLocalDiag X n v i π
  else heckeLeftRepresentative n i π (grassmannianCompletionGL X n v W)

/-- Equality of left `GL(O_v)`-cosets of two local general-linear matrices. -/
def SameLeftHeckeCoset (n : ℕ) (v : closedPoints X.left)
    (r s : GL (Fin n) (completion X v)) : Prop :=
  ∃ a : GL (Fin n) (completionIntegers X v),
    GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v)) a * r = s

/-- Distinct Grassmannian planes give distinct left integral cosets. The
plane is recovered as the reduction modulo `π` of the scaled row lattice. -/
theorem heckeLocalCosetRep_sameLeft_iff (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W W' : HeckeCosetIndex X n v i) (π : (completion X v)ˣ)
    (hπ : IsUniformizer X v π.val) :
    SameLeftHeckeCoset X n v (heckeLocalCosetRep X n v i W π)
      (heckeLocalCosetRep X n v i W' π) ↔ W = W' := sorry

/-- The Grassmannian section covers the spherical double coset exactly once
modulo left integral multiplication. -/
theorem heckeLocalCosetRep_complete (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (hi : i ≤ n) (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (a b : GL (Fin n) (completionIntegers X v)) :
    ∃! W : HeckeCosetIndex X n v i,
      SameLeftHeckeCoset X n v (heckeLocalCosetRep X n v i W π)
        (GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v)) a *
          satakeLocalDiag X n v i π *
          GeneralLinearGroup.map (ValuationSubring.subtype (completionIntegers X v)) b) :=
  sorry

/-- The degree-`n` representative is the scalar inverse uniformizer. -/
theorem heckeLocalCosetRep_last (n : ℕ) (v : closedPoints X.left)
    (W : HeckeCosetIndex X n v n) (π : (completion X v)ˣ) :
    heckeLocalCosetRep X n v n W π = GeneralLinearGroup.scalar (Fin n) π⁻¹ := sorry

/-- The line at infinity, spanned by `(1, 0)`, in the rank-two Grassmannian. -/
def heckeLineInfinity (v : closedPoints X.left) : HeckeCosetIndex X 2 v 1 :=
  HeckeCosetIndex.of X 2 v
    (Submodule.span (X.left.residueField v.1) {![1, 0]}) sorry

/-- The affine line spanned by `(-a, 1)`, corresponding to the off-diagonal
rank-two Hecke representative with residue parameter `a`. -/
def heckeLineAffine (v : closedPoints X.left) (a : X.left.residueField v.1) :
    HeckeCosetIndex X 2 v 1 :=
  HeckeCosetIndex.of X 2 v
    (Submodule.span (X.left.residueField v.1) {![-a, 1]}) sorry

/-- Infinity and the affine residue parameters enumerate the rank-two
Grassmannian without repetition. -/
theorem heckeLines_bijective (v : closedPoints X.left) :
    Function.Bijective (fun a : Option (X.left.residueField v.1) ↦
      a.elim (heckeLineInfinity X v) (heckeLineAffine X v)) := sorry

/-- A left `GL(O_v)`-coset representative in the spherical double coset,
obtained from the row-oriented Grassmannian section. -/
def heckeCosetRep (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W : HeckeCosetIndex X n v i) (π : (completion X v)ˣ) :
    GL (Fin n) (adeleRing X) :=
  embedLocalGL X n v (heckeLocalCosetRep X n v i W π)

/-- `heckeCosetRep` embeds the local left-coset representative. -/
theorem heckeCosetRep_spec (n : ℕ) (v : closedPoints X.left) (i : ℕ)
    (W : HeckeCosetIndex X n v i) (π : (completion X v)ˣ) :
    heckeCosetRep X n v i W π =
      embedLocalGL X n v (heckeLocalCosetRep X n v i W π) :=
  sorry

/-- The underlying function of the spherical Hecke operator `T_{v,i}`. -/
def heckeTGL_toFun [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (x : GL (Fin n) (adeleRing X)) : Λ :=
  ∑ W : HeckeCosetIndex X n (closedPointEmbed X U v) i,
    φ.toFun
      (heckeCosetRep X n (closedPointEmbed X U v) i W
          (chosenUniformizer X (closedPointEmbed X U v)) *
        x)

/-- The spherical Hecke operator `T_{v,i}` associated with the double coset
`GL(O_v) diag(π^{-1}^i, 1^{n-i}) GL(O_v)`. Preservation of the cusp-form laws
is deferred. -/
def heckeTGL [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) : CuspFormGL X n U Λ :=
  CuspFormGL.of (heckeTGL_toFun X n U v i φ) sorry sorry φ.level sorry sorry

/-- `heckeTGL` acts by the displayed sum of left translations over invertible
Grassmannian-frame representatives. -/
theorem heckeTGL_apply [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (x : GL (Fin n) (adeleRing X)) :
    (heckeTGL X n U v i φ).toFun x = heckeTGL_toFun X n U v i φ x := sorry

/-- The top-degree Hecke operator is a single translation by the scalar
inverse uniformizer, since the full Grassmannian has one point. -/
theorem heckeTGL_last_apply [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (x : GL (Fin n) (adeleRing X)) :
    (heckeTGL X n U v n φ).toFun x =
      φ.toFun (embedLocalGL X n (closedPointEmbed X U v)
        (GeneralLinearGroup.scalar (Fin n)
          (chosenUniformizer X (closedPointEmbed X U v))⁻¹) * x) := sorry

/-- `T_{v,i}(φ)(x)` is the sum of `φ(γ x)` over left `GL(O_v)`-coset
representatives `γ` in the spherical double coset of `satakeLocalDiag`, for
every uniformizer. -/
theorem heckeTGL_spec [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (π : (completion X (closedPointEmbed X U v))ˣ)
    (hπ : IsUniformizer X (closedPointEmbed X U v) π.val)
    (x : GL (Fin n) (adeleRing X)) :
    (heckeTGL X n U v i φ).toFun x =
      ∑ W : HeckeCosetIndex X n (closedPointEmbed X U v) i,
        φ.toFun (heckeCosetRep X n (closedPointEmbed X U v) i W π * x) :=
  sorry

/-- The operator `T_{v,i}` is independent of the choice of uniformizer. -/
theorem heckeTGL_independent [Finite k] (n : ℕ) (U : X.left.Opens)
    (v : closedPoints (openRestrict X U).left) (i : ℕ) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ)
    (π π' : (completion X (closedPointEmbed X U v))ˣ)
    (hπ : IsUniformizer X (closedPointEmbed X U v) π.val)
    (hπ' : IsUniformizer X (closedPointEmbed X U v) π'.val)
    (x : GL (Fin n) (adeleRing X)) :
    ∑ W : HeckeCosetIndex X n (closedPointEmbed X U v) i,
          φ.toFun (heckeCosetRep X n (closedPointEmbed X U v) i W π * x) =
      ∑ W : HeckeCosetIndex X n (closedPointEmbed X U v) i,
        φ.toFun (heckeCosetRep X n (closedPointEmbed X U v) i W π' * x) :=
  sorry

/-- The Satake/Hecke eigenvalue package of a `GL (Fin n)` eigenform on the open
`U`, recording the eigenvalues of `T_{v,i}` for `i = 1, …, n`. -/
structure EigenformGL (n : ℕ) (U : X.left.Opens) (Λ : Type v) [CommRing Λ] where
  /-- The Hecke eigenvalues of the operators `T_{v,i}` for
  `i = 1, …, n`. -/
  eigenvalue : closedPoints (openRestrict X U).left → Fin n → Λ

namespace EigenformGL

variable {X}
variable {n : ℕ} {U : X.left.Opens} {Λ : Type v} [CommRing Λ]

/-- The eigenvalue system with the given eigenvalue family. -/
def of (eigenvalue : closedPoints (openRestrict X U).left → Fin n → Λ) :
    EigenformGL X n U Λ where
  eigenvalue := eigenvalue

/-- The eigenvalue family of `of` is the given family. -/
theorem eigenvalue_apply
    (eigenvalue : closedPoints (openRestrict X U).left → Fin n → Λ) :
    (of eigenvalue).eigenvalue = eigenvalue := sorry

/-- An eigenvalue system is recovered from its eigenvalue family. -/
theorem spec (f : EigenformGL X n U Λ) : f = of f.eigenvalue := sorry

/-- The extended Satake eigenvalues, with `lambda v 0 = 1`. -/
def lambda (f : EigenformGL X n U Λ)
    (v : closedPoints (openRestrict X U).left) : Fin (n + 1) → Λ :=
  Fin.cases 1 fun j ↦ f.eigenvalue v j

/-- The zeroth Satake eigenvalue is `1`. -/
theorem lambda_zero (f : EigenformGL X n U Λ)
    (v : closedPoints (openRestrict X U).left) :
    lambda f v 0 = 1 := sorry

end EigenformGL

/-- The Satake polynomial
`∑ i, (-1)^i q^{Nat.choose i 2} * lam i * X^{n-i}` attached to a family of Hecke
eigenvalues. -/
def satakeCharpoly (n : ℕ) {Λ : Type v} [CommRing Λ]
    (q : ℕ) (lam : Fin (n + 1) → Λ) : Polynomial Λ :=
  ∑ i : Fin (n + 1),
    Polynomial.C ((-1 : Λ) ^ (i : ℕ) * (q : Λ) ^ Nat.choose (i : ℕ) 2 * lam i) *
      Polynomial.X ^ (n - (i : ℕ))

/-- Unfolding of `satakeCharpoly` as the displayed finite sum. -/
theorem satakeCharpoly_apply (n : ℕ) {Λ : Type v} [CommRing Λ]
    (q : ℕ) (lam : Fin (n + 1) → Λ) :
    satakeCharpoly n q lam =
      ∑ i : Fin (n + 1),
        Polynomial.C ((-1 : Λ) ^ (i : ℕ) * (q : Λ) ^ Nat.choose (i : ℕ) 2 * lam i) *
          Polynomial.X ^ (n - (i : ℕ)) := sorry

/-- For `n = 2`, the Satake polynomial of the `heckeT`/`heckeU` eigenvalues
`(t, u)` is `X^2 - t X + q * u`. -/
theorem satakeCharpoly_two {Λ : Type v} [CommRing Λ] (q : ℕ) (t u : Λ) :
    satakeCharpoly 2 q (Fin.cases 1 fun j : Fin 2 ↦ if j.val = 0 then t else u) =
      Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X +
        Polynomial.C ((q : Λ) * u) := sorry

namespace EigenformGL

variable {X}
variable {n : ℕ} {U : X.left.Opens} {Λ : Type v} [CommRing Λ]
/-- The Satake polynomial of `f` at a closed point of `U`. -/
def charpoly [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (openRestrict X U).left) : Polynomial Λ :=
  satakeCharpoly n (residueCard (openRestrict X U) v) (lambda f v)

/-- The Satake polynomial of `f` is `satakeCharpoly` of its extended
eigenvalues. -/
theorem charpoly_apply [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (openRestrict X U).left) :
    charpoly f v =
      satakeCharpoly n (residueCard (openRestrict X U) v) (lambda f v) :=
  sorry

/-- Each Satake polynomial is monic. -/
theorem charpoly_monic [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (openRestrict X U).left) :
    (charpoly f v).Monic := sorry

/-- Each Satake polynomial has natural degree `n`. -/
theorem natDegree_charpoly [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (openRestrict X U).left) :
    (charpoly f v).natDegree = n := sorry

/-- The last Satake eigenvalue `lambda v (Fin.last n)` is a unit of the valuation
ring of `PadicAlgCl ℓ`, equivalently
`(PadicAlgCl.valued ℓ).v (lambda v (Fin.last n)) = 1`. -/
def lambda_last_is_integral_unit {ℓ : ℕ} [Fact ℓ.Prime]
    (f : EigenformGL X n U (PadicAlgCl ℓ)) : Prop :=
  ∀ v, (PadicAlgCl.valued ℓ).v (lambda f v (Fin.last n)) = 1

/-- Unfolding of last-eigenvalue integrality as valuation exactly `1`. -/
theorem lambda_last_is_integral_unit_iff {ℓ : ℕ} [Fact ℓ.Prime]
    (f : EigenformGL X n U (PadicAlgCl ℓ)) :
    lambda_last_is_integral_unit f ↔
      ∀ v, (PadicAlgCl.valued ℓ).v (lambda f v (Fin.last n)) = 1 := sorry

/-- Last-eigenvalue integrality is equivalent to multiplicative norm `1`. -/
theorem lambda_last_nnnorm_eq_one_iff {ℓ : ℕ} [Fact ℓ.Prime]
    (f : EigenformGL X n U (PadicAlgCl ℓ)) :
    lambda_last_is_integral_unit f ↔
      ∀ v, ‖lambda f v (Fin.last n)‖₊ = 1 := sorry

/-- An eigenform `f` with values in `PadicAlgCl ℓ` is attached to a continuous
`GL (Fin n)`-valued representation `ρ` of `π₁(U)` when Satake polynomials match
geometric Frobenius characteristic polynomials after `Polynomial.map` to
`PadicAlgCl ℓ`. -/
def IsAttachedTo [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {xbar : GeometricPoint (openRestrict X U).left}
    [ConnectedSpace (openRestrict X U).left]
    {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup (openRestrict X U).left xbar →ₜ*
      GL (Fin n) E) : Prop :=
  ∀ (v : closedPoints (openRestrict X U).left)
    (ι : standardFiniteEtaleFiber
        (geometricPointOverClosedPoint (openRestrict X U) v) ≅
      standardFiniteEtaleFiber xbar),
    Polynomial.map (algebraMap E (PadicAlgCl ℓ))
        (Matrix.charpoly
          (ρ (etaleGeometricFrobenius (openRestrict X U) xbar v ι)).val) =
      f.charpoly v

/-- Unfolding of attachment as matching of Satake and Frobenius
characteristic polynomials. -/
theorem isAttachedTo_iff [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {xbar : GeometricPoint (openRestrict X U).left}
    [ConnectedSpace (openRestrict X U).left]
    {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup (openRestrict X U).left xbar →ₜ*
      GL (Fin n) E) :
    f.IsAttachedTo ρ ↔
      ∀ (v : closedPoints (openRestrict X U).left)
        (ι : standardFiniteEtaleFiber
            (geometricPointOverClosedPoint (openRestrict X U) v) ≅
          standardFiniteEtaleFiber xbar),
        Polynomial.map (algebraMap E (PadicAlgCl ℓ))
            (Matrix.charpoly
              (ρ (etaleGeometricFrobenius (openRestrict X U) xbar v ι)).val) =
          f.charpoly v := sorry

/-- Attached eigenforms recover Satake polynomials as mapped Frobenius
characteristic polynomials. -/
theorem isAttachedTo_charpoly [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {xbar : GeometricPoint (openRestrict X U).left}
    [ConnectedSpace (openRestrict X U).left]
    {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    {f : EigenformGL X n U (PadicAlgCl ℓ)}
    {ρ : etaleFundamentalGroup (openRestrict X U).left xbar →ₜ*
      GL (Fin n) E}
    (hf : f.IsAttachedTo ρ) (v : closedPoints (openRestrict X U).left)
    (ι : standardFiniteEtaleFiber
        (geometricPointOverClosedPoint (openRestrict X U) v) ≅
      standardFiniteEtaleFiber xbar) :
    f.charpoly v =
      Polynomial.map (algebraMap E (PadicAlgCl ℓ))
        (Matrix.charpoly
          (ρ (etaleGeometricFrobenius (openRestrict X U) xbar v ι)).val) :=
  sorry

end EigenformGL

/-- An unramified-on-`U` cusp form is a Hecke eigenform for the Satake package
`f` when some value is a unit and `T_{v, i} φ = eigenvalue v i • φ` for `i = 1, …, n`. -/
def IsEigenformGL [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ) : Prop :=
  (∃ x, IsUnit (φ.toFun x)) ∧
    ∀ (v : closedPoints (openRestrict X U).left) (i : Fin n),
      heckeTGL X n U v (i.val + 1) φ = (f.eigenvalue v i) • φ

/-- Unfolding of the ramified `GL (Fin n)` eigenform predicate. -/
theorem isEigenformGL_iff [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ) :
    IsEigenformGL X n U φ f ↔
      (∃ x, IsUnit (φ.toFun x)) ∧
        ∀ (v : closedPoints (openRestrict X U).left) (i : Fin n),
          heckeTGL X n U v (i.val + 1) φ =
            (f.eigenvalue v i) • φ := sorry

/-- A ramified `GL (Fin n)` eigenform takes a unit value. -/
theorem isEigenformGL_isUnit [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ)
    (hφ : IsEigenformGL X n U φ f) : ∃ x, IsUnit (φ.toFun x) := sorry

/-- A ramified `GL (Fin n)` eigenform is a `T_{v,i}`-eigenvector with eigenvalue
`f.eigenvalue v i`. -/
theorem isEigenformGL_heckeTGL [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ)
    (hφ : IsEigenformGL X n U φ f)
    (v : closedPoints (openRestrict X U).left) (i : Fin n) :
    heckeTGL X n U v (i.val + 1) φ =
      (f.eigenvalue v i) • φ := sorry

end AlgebraicGeometry.SchemeOverField
