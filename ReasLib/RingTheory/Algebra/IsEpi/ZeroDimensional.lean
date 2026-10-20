module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

noncomputable section

namespace ZeroDimEpi

open MvPolynomial

/-- The two families of source variables `x i` and `z i` for `i ≥ 1`. -/
inductive SrcVar
  | x : ℕ+ → SrcVar
  | z : ℕ+ → SrcVar
  deriving DecidableEq

/-- The two families of target variables `x i` and `y i` for `i ≥ 1`. -/
inductive TgtVar
  | x : ℕ+ → TgtVar
  | y : ℕ+ → TgtVar
  deriving DecidableEq

/-- The source ℤ-grading of variables, with `deg x i = -1` and `deg z i = 0`. -/
def srcDeg : SrcVar → ℤ
  | .x _ => -1
  | .z _ => 0

/-- The target ℤ-grading of variables, with `deg x i = -1` and `deg y i = 1`. -/
def tgtDeg : TgtVar → ℤ
  | .x _ => -1
  | .y _ => 1

variable (k : Type u)

section

variable [CommRing k]

/-- The source relation `X i ^ (4 ^ i)`. -/
def srcXPow (i : ℕ+) : MvPolynomial SrcVar k :=
  X (.x i) ^ (4 ^ (i : ℕ))

/-- The source relation `Z i ^ (4 ^ i)`. -/
def srcZPow (i : ℕ+) : MvPolynomial SrcVar k :=
  X (.z i) ^ (4 ^ (i : ℕ))

/-- The target relation `X i ^ (4 ^ i)`. -/
def tgtXPow (i : ℕ+) : MvPolynomial TgtVar k :=
  X (.x i) ^ (4 ^ (i : ℕ))

/-- The target relation `Y i - X (i + 1) * Y (i + 1) ^ 2`. -/
def tgtYRecurrence (i : ℕ+) : MvPolynomial TgtVar k :=
  X (.y i) - X (.x (i + 1)) * X (.y (i + 1)) ^ 2

/-- The defining ideal `(x i ^ (4 ^ i), z i ^ (4 ^ i))` of the source presentation. -/
def srcIdeal : Ideal (MvPolynomial SrcVar k) :=
  Ideal.span (Set.range (srcXPow k) ∪ Set.range (srcZPow k))

/-- The defining ideal `(x i ^ (4 ^ i), y i - x (i + 1) y (i + 1) ^ 2)` of the target
presentation. -/
def tgtIdeal : Ideal (MvPolynomial TgtVar k) :=
  Ideal.span (Set.range (tgtXPow k) ∪ Set.range (tgtYRecurrence k))

/-- The source ring `k[x i, z i] ⧸ (x i ^ (4 ^ i), z i ^ (4 ^ i))`. -/
abbrev Src : Type u := MvPolynomial SrcVar k ⧸ srcIdeal k

/-- The target ring `k[x i, y i] ⧸ (x i ^ (4 ^ i), y i - x (i + 1) y (i + 1) ^ 2)`. -/
abbrev Tgt : Type u := MvPolynomial TgtVar k ⧸ tgtIdeal k

/-- The image of `x i` in the source quotient. -/
def srcX (i : ℕ+) : Src k :=
  Ideal.Quotient.mk (srcIdeal k) (X (.x i))

/-- The image of `z i` in the source quotient. -/
def srcZ (i : ℕ+) : Src k :=
  Ideal.Quotient.mk (srcIdeal k) (X (.z i))

/-- The image of `x i` in the target quotient. -/
def tgtX (i : ℕ+) : Tgt k :=
  Ideal.Quotient.mk (tgtIdeal k) (X (.x i))

/-- The image of `y i` in the target quotient. -/
def tgtY (i : ℕ+) : Tgt k :=
  Ideal.Quotient.mk (tgtIdeal k) (X (.y i))

/-- The polynomial-level comparison sending `x i` to `x i` and `z i` to `x i * y i`. -/
def srcToTgt : MvPolynomial SrcVar k →ₐ[k] MvPolynomial TgtVar k :=
  aeval fun v ↦
    match v with
    | .x i => X (TgtVar.x i)
    | .z i => X (TgtVar.x i) * X (TgtVar.y i)

/-- The source relations vanish after the comparison map into the target quotient. -/
theorem srcToTgt_mem :
    ∀ p ∈ srcIdeal k, ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom) p = 0 :=
  sorry

/-- The induced homomorphism of presentations. -/
def hom : Src k →+* Tgt k :=
  Ideal.Quotient.lift (srcIdeal k) ((Ideal.Quotient.mk (tgtIdeal k)).comp (srcToTgt k).toRingHom)
    (srcToTgt_mem k)

/-- The canonical `Src`-algebra structure on `Tgt` induced by `hom`. -/
instance instAlgebra : Algebra (Src k) (Tgt k) :=
  (hom k).toAlgebra

/-- The comparison map sends `srcX i` to `tgtX i`. -/
theorem hom_srcX (i : ℕ+) : hom k (srcX k i) = tgtX k i := sorry

/-- The comparison map sends `srcZ i` to `tgtX i * tgtY i`. -/
theorem hom_srcZ (i : ℕ+) : hom k (srcZ k i) = tgtX k i * tgtY k i := sorry

/-- The source generators `srcX i` are nilpotent of index `4 ^ i`. -/
theorem srcX_pow_eq_zero (i : ℕ+) : srcX k i ^ (4 ^ (i : ℕ)) = 0 := sorry

/-- The source generators `srcZ i` are nilpotent of index `4 ^ i`. -/
theorem srcZ_pow_eq_zero (i : ℕ+) : srcZ k i ^ (4 ^ (i : ℕ)) = 0 := sorry

/-- The target generators `tgtX i` are nilpotent of index `4 ^ i`. -/
theorem tgtX_pow_eq_zero (i : ℕ+) : tgtX k i ^ (4 ^ (i : ℕ)) = 0 := sorry

/-- The target generators satisfy the recurrence `y i = x (i + 1) * y (i + 1) ^ 2`. -/
theorem tgtY_eq (i : ℕ+) : tgtY k i = tgtX k (i + 1) * tgtY k (i + 1) ^ 2 := sorry

/-- Each `y i` is nilpotent of index `4 ^ (i + 1)`. -/
theorem tgtY_pow_eq_zero (i : ℕ+) : tgtY k i ^ (4 ^ ((i : ℕ) + 1)) = 0 := sorry

end

section

variable [Field k]

/-- The source presentation is a local ring. -/
instance instIsLocalRingSrc : IsLocalRing (Src k) := sorry

/-- The target presentation is a local ring. -/
instance instIsLocalRingTgt : IsLocalRing (Tgt k) := sorry

/-- The source presentation has Krull dimension at most `0`. -/
instance instKrullDimLESrc : Ring.KrullDimLE 0 (Src k) := sorry

/-- The target presentation has Krull dimension at most `0`. -/
instance instKrullDimLETgt : Ring.KrullDimLE 0 (Tgt k) := sorry

/-- The comparison map is an epimorphism of commutative rings. -/
instance instIsEpi : Algebra.IsEpi (Src k) (Tgt k) := sorry

/-- The generator `y 1` is nonzero in the target. -/
theorem tgtY_one_ne_zero : tgtY k 1 ≠ 0 := sorry

/-- The comparison map is not surjective. -/
theorem not_surjective : ¬ Function.Surjective (hom k) := sorry

end

end ZeroDimEpi

namespace RingHom

/-- There exists a nonsurjective epimorphism between local commutative rings of Krull
dimension zero. -/
@[stacks 06RI]
theorem exists_isLocalRing_krullDimLE_zero_isEpi_not_surjective :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S)
      (_ : IsLocalRing R) (_ : IsLocalRing S) (_ : Ring.KrullDimLE 0 R)
      (_ : Ring.KrullDimLE 0 S),
      Algebra.IsEpi R S ∧ ¬ Function.Surjective (algebraMap R S) := sorry

end RingHom
