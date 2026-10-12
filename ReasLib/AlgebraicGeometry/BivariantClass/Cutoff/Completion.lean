/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.GroupTheory.Submonoid.Center
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic

/-!
# Cutoff families `A⁽ᵖ⁾(Z ⟶ X)`

Nonnegative completed cutoff families, with the valid fixed-cutoff `p = 1`
Cauchy convolution. General sum-cutoff products live in `Cutoff.SumProduct`.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cutoff

/-- The completed cutoff family: ambient Chow cohomology in degrees `n < p`, and
bivariant classes of the closed immersion from degree `p` onward. -/
abbrev Family
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] (p : ℕ) : Type (u + 1) :=
  ∀ n : ℕ, Cutoff δ f p n

/-- `Family` is the dependent product of all nonnegative cutoff degrees. -/
theorem family_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] (p : ℕ) :
    Family δ f p = ∀ n : ℕ, Cutoff δ f p n := sorry

namespace Family

/-- Two cutoff families are equal when all coefficients agree. -/
@[ext]
theorem ext
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    {f : Z ⟶ X} [IsClosedImmersion f.left] {p : ℕ} {a b : Family δ f p}
    (h : ∀ n, a n = b n) : a = b := sorry

/-- The convolution unit of the source cutoff `A⁽¹⁾(Z ⟶ X)`: the identity class
of `X` in degree `0`, and zero in every positive degree. -/
def one
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] : Family δ f 1
  | 0 => ofAmbient δ f (Nat.cast_lt.mpr Nat.zero_lt_one) (ChowCohomology.one δ X.hom)
  | _ + 1 => 0

/-- The degree-zero coefficient of the convolution unit is the identity class of `X`. -/
theorem one_apply_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] :
    one δ f 0 = ofAmbient δ f (Nat.cast_lt.mpr Nat.zero_lt_one)
      (ChowCohomology.one δ X.hom) :=
  sorry

/-- Every positive-degree coefficient of the convolution unit vanishes. -/
theorem one_apply_succ
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] (n : ℕ) :
    one δ f (n + 1) = 0 := sorry

/-- The homogeneous mixed product of two coefficients in the source cutoff `p = 1`.
Ambient-ambient products occur only in degree `0`; every other antidiagonal factor
uses a Remark 42.34.7 mixed product into a relative degree. -/
def mulTerm
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] {i j n : ℕ} (hij : i + j = n)
    (c : Cutoff δ f 1 i) (d : Cutoff δ f 1 j) : Cutoff δ f 1 n :=
  if hn : n < 1 then
    ofAmbient δ f (Nat.cast_lt.mpr hn)
      (Eq.mp (congrArg (ChowCohomology.Nonnegative.degree δ X.hom) hij)
        (ChowCohomology.Nonnegative.mul δ X.hom
          (toAmbient δ f
            (Nat.cast_lt.mpr
              (lt_of_le_of_lt (Nat.le_add_right i j) (hij.symm ▸ hn))) c)
          (toAmbient δ f
            (Nat.cast_lt.mpr
              (lt_of_le_of_lt (Nat.le_add_left j i) (hij.symm ▸ hn))) d)))
  else if hi : i < 1 then
    ofRelative δ f (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt hn)))
      (Nonnegative.castGrading δ
        ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
        (ambientMulRelative δ f i j
          (toAmbient δ f (Nat.cast_lt.mpr hi) c)
          (toRelative δ f
            (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt
              (((Nat.zero_add j).symm.trans (Nat.lt_one_iff.mp hi ▸ hij)).symm ▸ hn))))
            d)))
  else if hj : j < 1 then
    ofRelative δ f (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt hn)))
      (Nonnegative.castGrading δ
        ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
        (relativeMulAmbient δ f i j
          (toRelative δ f
            (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt
              (((Nat.add_zero i).symm.trans (Nat.lt_one_iff.mp hj ▸ hij)).symm ▸ hn))))
            c)
          (toAmbient δ f (Nat.cast_lt.mpr hj) d)))
  else
    ofRelative δ f (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt hn)))
      (Nonnegative.castGrading δ
        ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
        (relativeMul δ f i j
          (toRelative δ f (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt hi))) c)
          (toRelative δ f (not_lt.mpr (Nat.cast_le.mpr (le_of_not_gt hj))) d)))

/-- Finite Cauchy convolution on `A⁰(X) × ∏_{i≥1} Aⁱ(Z ⟶ X)`, using ambient
multiplication in degree `0` and the mixed Remark 42.34.7 products from degree `1`. -/
def mul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a b : Family δ f 1) : Family δ f 1 :=
  fun n ↦ (Finset.antidiagonal n).attach.sum fun ij ↦
    mulTerm δ f (Finset.mem_antidiagonal.mp ij.property) (a ij.1.1) (b ij.1.2)

/-- Multiplication is coefficientwise finite Cauchy convolution. -/
theorem mul_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a b : Family δ f 1) (n : ℕ) :
    mul δ f a b n =
      (Finset.antidiagonal n).attach.sum fun ij ↦
        mulTerm δ f (Finset.mem_antidiagonal.mp ij.property) (a ij.1.1) (b ij.1.2) :=
  sorry

/-- The canonical unit on the source cutoff family `A⁽¹⁾(Z ⟶ X)`. -/
noncomputable instance instOne
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] :
    One (Family δ f 1) :=
  ⟨one δ f⟩

/-- The canonical convolution multiplication on the source cutoff family `A⁽¹⁾(Z ⟶ X)`. -/
noncomputable instance instMul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] :
    Mul (Family δ f 1) :=
  ⟨mul δ f⟩

/-- Convolution multiplication of source cutoff families is associative. -/
theorem mul_assoc_axiom
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] (a b c : Family δ f 1) :
    a * b * c = a * (b * c) := sorry

/-- The convolution unit is a left unit. -/
theorem one_mul_axiom
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] (a : Family δ f 1) :
    1 * a = a := sorry

/-- The convolution unit is a right unit. -/
theorem mul_one_axiom
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] (a : Family δ f 1) :
    a * 1 = a := sorry

/-- The canonical monoid of source cutoff families under Cauchy convolution.
The Remark 42.34.7 product is order-sensitive, so this is not a `CommMonoid`. -/
noncomputable instance instMonoid
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left] :
    Monoid (Family δ f 1) where
  mul := mul δ f
  one := one δ f
  mul_assoc := mul_assoc_axiom δ f
  one_mul := one_mul_axiom δ f
  mul_one := mul_one_axiom δ f

/-- The recursive Cauchy inverse of a source cutoff family, normalized so that the
constant term is the convolution unit. -/
def formalInverse
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) : Family δ f 1 :=
  WellFounded.fix (C := fun n : ℕ ↦ Cutoff δ f 1 n)
    (inferInstance : WellFoundedRelation ℕ).wf fun n rec ↦
      if h : n = 0 then
        Eq.mpr (congrArg (fun k : ℕ ↦ Cutoff δ f 1 k) h) (one δ f 0)
      else
        -((Finset.range n).sum fun k ↦
            if hk : k < n then
              mulTerm δ f (Nat.add_sub_of_le (Nat.succ_le_of_lt hk))
                (a (k + 1))
                (rec (n - (k + 1)) (Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.succ_pos k)))
            else
              0)

/-- The constant coefficient of the formal inverse is the convolution unit. -/
theorem formalInverse_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) :
    formalInverse δ f a 0 = one δ f 0 := sorry

/-- A cutoff family with unit constant coefficient multiplies its formal inverse to one. -/
theorem mul_formalInverse
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) (ha : a 0 = one δ f 0) :
    a * formalInverse δ f a = 1 := sorry

/-- The formal inverse of a cutoff family with unit constant coefficient multiplies it
to one. -/
theorem formalInverse_mul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) (ha : a 0 = one δ f 0) :
    formalInverse δ f a * a = 1 := sorry

/-- The formal inverse of a central cutoff family with unit constant coefficient is central. -/
theorem formalInverse_mem_center
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) (ha : a 0 = one δ f 0)
    (hcentral : a ∈ Set.center (Family δ f 1)) :
    formalInverse δ f a ∈ Set.center (Family δ f 1) := sorry

/-- Package a central cutoff family with unit constant coefficient as a unit of the center. -/
def unitOf
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) (ha : a 0 = one δ f 0)
    (hcentral : a ∈ Set.center (Family δ f 1)) :
    (Submonoid.center (Family δ f 1))ˣ where
  val := ⟨a, hcentral⟩
  inv := ⟨formalInverse δ f a, formalInverse_mem_center δ f a ha hcentral⟩
  val_inv := Subtype.ext (mul_formalInverse δ f a ha)
  inv_val := Subtype.ext (formalInverse_mul δ f a ha)

/-- The value of `unitOf` is the cutoff family supplied to it. -/
theorem unitOf_val
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (a : Family δ f 1) (ha : a 0 = one δ f 0)
    (hcentral : a ∈ Set.center (Family δ f 1)) :
    (unitOf δ f a ha hcentral).val.val = a := sorry

end Family

end AlgebraicGeometry.BivariantClass.Cutoff
