module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.DirectSum.Ring
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap82.Remark_82_28_5_ChernClass

/-!
# Tensor-twist formula for Chern classes on algebraic spaces

The binomial identity for `c_i(E ⊗ L)` in the Chow cohomology ring `A^*(X)` of
a good algebraic space, using the operational classes of Remark 82.28.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators DirectSum MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Invertible `𝒪_X`-modules are finite locally free. -/
instance instIsFiniteLocallyFree_of_isInvertibleObject {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] :
    SheafOfModules.IsFiniteLocallyFree L :=
  sorry

/-- Finite locally free `𝒪_X`-modules are closed under tensor product. -/
instance instIsFiniteLocallyFree_tensor {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E L : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    [SheafOfModules.IsFiniteLocallyFree L] :
    SheafOfModules.IsFiniteLocallyFree (E ⊗ L) :=
  sorry

namespace ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

/-- Pointwise addition of identity classes. -/
def addCap {p : ℤ} (c d : degree δ f p) : degree δ f p :=
  ofCap δ f
    (fun {Y} (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (k : ℤ) ↦ c.cap g k + d.cap g k)
    sorry sorry sorry

/-- Evaluation of pointwise addition is addition of the evaluated maps. -/
theorem addCap_apply {p : ℤ} (c d : degree δ f p) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) :
    (addCap δ f c d).cap g k = c.cap g k + d.cap g k :=
  sorry

/-- Pointwise negation of an identity class. -/
def negCap {p : ℤ} (c : degree δ f p) : degree δ f p :=
  ofCap δ f
    (fun {Y} (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (k : ℤ) ↦ -c.cap g k)
    sorry sorry sorry

/-- Evaluation of pointwise negation is negation of the evaluated map. -/
theorem negCap_apply {p : ℤ} (c : degree δ f p) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) :
    (negCap δ f c).cap g k = -c.cap g k :=
  sorry

/-- Natural scalar multiplication of an identity class. -/
def nsmulCap {p : ℤ} (n : ℕ) (c : degree δ f p) : degree δ f p :=
  ofCap δ f
    (fun {Y} (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (k : ℤ) ↦ n • c.cap g k)
    sorry sorry sorry

/-- Natural scalar multiplication evaluates pointwise. -/
theorem nsmulCap_apply {p : ℤ} (n : ℕ) (c : degree δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (nsmulCap δ f n c).cap g k = n • c.cap g k :=
  sorry

/-- Integer scalar multiplication of an identity class. -/
def zsmulCap {p : ℤ} (z : ℤ) (c : degree δ f p) : degree δ f p :=
  ofCap δ f
    (fun {Y} (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (k : ℤ) ↦ z • c.cap g k)
    sorry sorry sorry

/-- Integer scalar multiplication evaluates pointwise. -/
theorem zsmulCap_apply {p : ℤ} (z : ℤ) (c : degree δ f p)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (zsmulCap δ f z c).cap g k = z • c.cap g k :=
  sorry

/-- Every identity bivariant degree is an additive commutative group under
pointwise operations. -/
instance instAddCommGroupDegree (p : ℤ) : AddCommGroup (degree δ f p) where
  zero := zeroCap δ f p
  add := addCap δ f
  neg := negCap δ f
  sub := fun c d ↦ addCap δ f c (negCap δ f d)
  nsmul := nsmulCap δ f
  zsmul := zsmulCap δ f
  zero_add := sorry
  add_zero := sorry
  add_assoc := sorry
  add_comm := sorry
  neg_add_cancel := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  sub_eq_add_neg := sorry

/-- Composition of identity caps reindexes along `(k - q) - p = k - (p + q)`. -/
theorem mulCap_degree_eq (k p q : ℤ) : (k - q) - p = k - (p + q) :=
  sorry

/-- Homogeneous multiplication is composition of identity bivariant classes,
with the right factor acting first. -/
def mulCap {p q : ℤ} (c : degree δ f p) (d : degree δ f q) :
    degree δ f (p + q) :=
  ofCap δ f
    (fun {Y} (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (k : ℤ) ↦
      (castChowGroup δ (g ≫ f) (mulCap_degree_eq k p q)).comp
        ((c.cap g (k - q)).comp (d.cap g k)))
    sorry sorry sorry

/-- Cap-family multiplication is composition of the shifted additive maps,
reindexed along `(k - q) - p = k - (p + q)`. -/
theorem mulCap_apply {p q : ℤ} (c : degree δ f p) (d : degree δ f q)
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (mulCap δ f c d).cap g k =
      (castChowGroup δ (g ≫ f) (mulCap_degree_eq k p q)).comp
        ((c.cap g (k - q)).comp (d.cap g k)) :=
  sorry

/-- Natural-number casts in degree zero, as multiples of the identity class. -/
def natCastCap (n : ℕ) : degree δ f 0 :=
  nsmulCap δ f n (oneCap δ f)

/-- `natCastCap n` is `n` copies of the identity class. -/
theorem natCastCap_eq (n : ℕ) :
    natCastCap δ f n = nsmulCap δ f n (oneCap δ f) :=
  sorry

/-- Integer casts in degree zero. -/
def intCastCap (z : ℤ) : degree δ f 0 :=
  zsmulCap δ f z (oneCap δ f)

/-- `intCastCap z` is the integer multiple of the identity class. -/
theorem intCastCap_eq (z : ℤ) :
    intCastCap δ f z = zsmulCap δ f z (oneCap δ f) :=
  sorry

/-- The Chow cohomology ring `A^*(X)` of a good algebraic space `X / B`. -/
abbrev ring : Type (u + 1) :=
  ⨁ p : ℤ, degree δ f p

/-- Chow cohomology is the external direct sum of the identity bivariant
groups. -/
theorem ring_def : ring δ f = ⨁ p : ℤ, degree δ f p :=
  sorry

/-- Homogeneous multiplication by zero on the right vanishes. -/
theorem mulCap_zero {p q : ℤ} (c : degree δ f p) :
    mulCap δ f c (0 : degree δ f q) = 0 :=
  sorry

/-- Homogeneous multiplication by zero on the left vanishes. -/
theorem zero_mulCap {p q : ℤ} (d : degree δ f q) :
    mulCap δ f (0 : degree δ f p) d = 0 :=
  sorry

/-- Homogeneous multiplication distributes over addition in the right
variable. -/
theorem mulCap_add {p q : ℤ} (c : degree δ f p) (d e : degree δ f q) :
    mulCap δ f c (d + e) = mulCap δ f c d + mulCap δ f c e :=
  sorry

/-- Homogeneous multiplication distributes over addition in the left
variable. -/
theorem add_mulCap {p q : ℤ} (c d : degree δ f p) (e : degree δ f q) :
    mulCap δ f (c + d) e = mulCap δ f c e + mulCap δ f d e :=
  sorry

/-- Natural-number casts send zero to zero. -/
theorem natCastCap_zero : natCastCap δ f 0 = 0 :=
  sorry

/-- Natural-number casts respect successors. -/
theorem natCastCap_succ (n : ℕ) :
    natCastCap δ f (n + 1) = natCastCap δ f n + oneCap δ f :=
  sorry

/-- Integer casts extend natural-number casts. -/
theorem intCastCap_ofNat (n : ℕ) : intCastCap δ f n = natCastCap δ f n :=
  sorry

/-- Integer casts of negative successors are negatives of natural-number
casts. -/
theorem intCastCap_negSucc (n : ℕ) :
    intCastCap δ f (Int.negSucc n) = -(natCastCap δ f (n + 1)) :=
  sorry

/-- Graded ring operations on identity bivariant classes, with real
one/mul/natCast/intCast data. -/
instance instGRing : DirectSum.GRing (degree δ f) where
  mul := mulCap δ f
  mul_zero := mulCap_zero δ f
  zero_mul := zero_mulCap δ f
  mul_add := mulCap_add δ f
  add_mul := add_mulCap δ f
  one := oneCap δ f
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry
  natCast := natCastCap δ f
  natCast_zero := natCastCap_zero δ f
  natCast_succ := natCastCap_succ δ f
  intCast := intCastCap δ f
  intCast_ofNat := intCastCap_ofNat δ f
  intCast_negSucc_ofNat := intCastCap_negSucc δ f

/-- The Chow cohomology ring `A^*(X)` carries the ring structure induced by
graded composition of identity bivariant classes. -/
instance instRing : Ring (ring δ f) :=
  inferInstanceAs (Ring (⨁ p : ℤ, degree δ f p))

/-- Embed a homogeneous identity class in the full Chow cohomology ring. -/
def homogeneous (p : ℤ) (c : degree δ f p) : ring δ f :=
  DirectSum.of (degree δ f) p c

/-- `homogeneous p c` is the direct-sum inclusion of the degree-`p` class. -/
theorem homogeneous_eq (p : ℤ) (c : degree δ f p) :
    homogeneous δ f p c = DirectSum.of (degree δ f) p c :=
  sorry

end ChowCohomology

/-- For a good algebraic space `X` over a universally catenary quasi-separated
base `B`, a finite locally free `𝒪_X`-module `E` of rank `r`, and an invertible
`𝒪_X`-module `L`, the degree-`i` operational Chern class of `E ⊗ L` equals the
corresponding binomial sum in Chow cohomology of `X` relative to `f` and `δ`. -/
theorem chernClass_tensor_invertible {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (E L : X.Modules) (r i : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] [isInvertibleObject L] :
    ChowCohomology.homogeneous δ f i (ChernClass.chernClass δ f (E ⊗ L) i) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j : ChowCohomology.ring δ f) *
          ChowCohomology.homogeneous δ f (i - j : ℕ)
            (ChernClass.chernClass δ f E (i - j)) *
            ChowCohomology.homogeneous δ f 1 (ChernClass.chernClass δ f L 1) ^ j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
