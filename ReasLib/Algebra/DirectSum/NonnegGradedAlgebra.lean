module

public import ReasLib.Algebra.DirectSum.GradedCommutative

/-!
# Bundled nonnegatively graded algebras

This file bundles a family of homogeneous pieces carrying Mathlib's external direct-sum algebra
classes. It also exposes the even, odd, and positive-even direct sums and the parity-sensitive
multiplication maps used by divided powers on graded algebras.
-/

@[expose] public section

open scoped DirectSum

universe u v

/-- A bundled nonnegatively graded algebra whose homogeneous pieces use Mathlib's
`DirectSum.GSemiring` and `DirectSum.GAlgebra` structures. -/
structure NonnegGradedAlgebra (R : Type u) [CommRing R] where
  /-- The homogeneous piece in each nonnegative degree. -/
  piece : ℕ → Type v
  /-- Additive group structure on the homogeneous pieces. -/
  [pieceAddCommGroup : ∀ n : ℕ, AddCommGroup (piece n)]
  /-- Scalar multiplication on the homogeneous pieces. -/
  [pieceModule : ∀ n : ℕ, Module R (piece n)]
  /-- Homogeneous multiplication and its graded semiring laws. -/
  [pieceGSemiring : DirectSum.GSemiring piece]
  /-- The graded algebra structure over `R`. -/
  [pieceGAlgebra : DirectSum.GAlgebra R piece]
  /-- Strict graded commutativity of homogeneous multiplication. -/
  [pieceIsStrictlyCommutative : DirectSum.Graded.IsStrictlyCommutative R piece]

attribute [instance] NonnegGradedAlgebra.pieceAddCommGroup
attribute [instance] NonnegGradedAlgebra.pieceModule
attribute [instance] NonnegGradedAlgebra.pieceGSemiring
attribute [instance] NonnegGradedAlgebra.pieceGAlgebra
attribute [instance] NonnegGradedAlgebra.pieceIsStrictlyCommutative

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)

/-- The unit in degree zero, selected from the bundled graded algebra. -/
abbrev one : A.piece 0 :=
  GradedMonoid.GOne.one

/-- Multiplication of homogeneous elements, selected from the bundled graded algebra. -/
abbrev mul {m n : ℕ} : A.piece m → A.piece n → A.piece (m + n) :=
  GradedMonoid.GMul.mul

/-- The family of even homogeneous pieces. -/
abbrev evenFamily : ℕ → Type v :=
  fun d ↦ A.piece (2 * d)

/-- The family of odd homogeneous pieces. -/
abbrev oddFamily : ℕ → Type v :=
  fun d ↦ A.piece (2 * d + 1)

/-- The direct sum of all even homogeneous pieces. -/
abbrev evenPart : Type v :=
  ⨁ d : ℕ, A.piece (2 * d)

/-- The direct sum of all odd homogeneous pieces. -/
abbrev oddPart : Type v :=
  ⨁ d : ℕ, A.piece (2 * d + 1)

/-- The direct sum of all positive even homogeneous pieces. -/
abbrev evenPositivePart : Type v :=
  ⨁ d : ℕ, A.piece (2 * (d + 1))

/-- The inherited additive structure on an even homogeneous piece. -/
instance evenFamilyAddCommMonoid (d : ℕ) : AddCommMonoid (A.evenFamily d) :=
  inferInstance

/-- The inherited module structure on an even homogeneous piece. -/
instance evenFamilyModule (d : ℕ) : Module R (A.evenFamily d) :=
  A.pieceModule (2 * d)

/-- The inherited additive structure on an odd homogeneous piece. -/
instance oddFamilyAddCommMonoid (d : ℕ) : AddCommMonoid (A.oddFamily d) :=
  inferInstance

/-- The inherited module structure on an odd homogeneous piece. -/
instance oddFamilyModule (d : ℕ) : Module R (A.oddFamily d) :=
  A.pieceModule (2 * d + 1)

/-- The additive structure on the even direct sum. -/
instance evenPartAddCommMonoid : AddCommMonoid A.evenPart :=
  instAddCommMonoidDirectSum ℕ (fun d ↦ A.piece (2 * d))

/-- The module structure on the even direct sum. -/
instance evenPartModule : Module R A.evenPart :=
  DirectSum.instModule

/-- The additive structure on the odd direct sum. -/
instance oddPartAddCommMonoid : AddCommMonoid A.oddPart :=
  instAddCommMonoidDirectSum ℕ (fun d ↦ A.piece (2 * d + 1))

/-- The module structure on the odd direct sum. -/
instance oddPartModule : Module R A.oddPart :=
  DirectSum.instModule

/-- The additive structure on the positive-even direct sum. -/
instance evenPositivePartAddCommMonoid : AddCommMonoid A.evenPositivePart :=
  instAddCommMonoidDirectSum ℕ (fun d ↦ A.piece (2 * (d + 1)))

/-- The module structure on the positive-even direct sum. -/
instance evenPositivePartModule : Module R A.evenPositivePart :=
  DirectSum.instModule

/-- Casting a homogeneous piece along a degree equality preserves addition. -/
theorem pieceCast_map_add {m n : ℕ} (h : m = n) (x y : A.piece m) :
    cast (congrArg A.piece h) (x + y) =
      cast (congrArg A.piece h) x + cast (congrArg A.piece h) y := sorry

/-- Casting a homogeneous piece along a degree equality preserves scalar multiplication. -/
theorem pieceCast_map_smul {m n : ℕ} (h : m = n) (r : R) (x : A.piece m) :
    cast (congrArg A.piece h) (r • x) = r • cast (congrArg A.piece h) x := sorry

/-- Reindexing a homogeneous piece along an equality of degrees. -/
def pieceCast {m n : ℕ} (h : m = n) : A.piece m →ₗ[R] A.piece n :=
  h ▸ LinearMap.id

/-- The homogeneous degree-`2 * d` inclusion into the even part. -/
abbrev evenHom (d : ℕ) : A.piece (2 * d) →ₗ[R] A.evenPart :=
  DirectSum.lof R ℕ (fun e ↦ A.piece (2 * e)) d

/-- The homogeneous degree-`2 * (d + 1)` inclusion into the positive-even part. -/
abbrev evenPositiveHom (d : ℕ) :
    A.piece (2 * (d + 1)) →ₗ[R] A.evenPositivePart :=
  DirectSum.lof R ℕ (fun e ↦ A.piece (2 * (e + 1))) d

/-- The canonical inclusion from the positive-even part into the even part. -/
def evenPositiveToEven : A.evenPositivePart →ₗ[R] A.evenPart :=
  DirectSum.toModule R ℕ A.evenPart fun d ↦ A.evenHom (d + 1)

/-- The positive-even inclusion agrees with the homogeneous inclusions. -/
@[simp]
theorem evenPositiveToEven_evenPositiveHom (d : ℕ) (x : A.piece (2 * (d + 1))) :
    A.evenPositiveToEven (A.evenPositiveHom d x) = A.evenHom (d + 1) x := sorry

/-- The submodule of the even part generated by all positive even pieces. -/
def evenPositiveSubmodule : Submodule R A.evenPart :=
  LinearMap.range A.evenPositiveToEven

/-- Every positive even homogeneous element belongs to the positive-even submodule. -/
theorem evenHom_mem_evenPositiveSubmodule (d : ℕ) (x : A.piece (2 * (d + 1))) :
    A.evenHom (d + 1) x ∈ A.evenPositiveSubmodule := sorry

/-- The homogeneous degree-`2 * d + 1` inclusion into the odd part. -/
abbrev oddHom (d : ℕ) : A.piece (2 * d + 1) →ₗ[R] A.oddPart :=
  DirectSum.lof R ℕ (fun e ↦ A.piece (2 * e + 1)) d

/-- The projection from the even part onto its positive-degree summands. -/
def evenToEvenPositive : A.evenPart →ₗ[R] A.evenPositivePart :=
  DirectSum.toModule R ℕ A.evenPositivePart fun
    | 0 => 0
    | d + 1 => A.evenPositiveHom d

/-- The positive-degree projection kills the degree-zero summand. -/
@[simp]
theorem evenToEvenPositive_evenHom_zero (x : A.piece 0) :
    A.evenToEvenPositive (A.evenHom 0 x) = 0 := sorry

/-- The positive-degree projection is the identity on a positive even homogeneous summand. -/
@[simp]
theorem evenToEvenPositive_evenHom_succ (d : ℕ) (x : A.piece (2 * (d + 1))) :
    A.evenToEvenPositive (A.evenHom (d + 1) x) = A.evenPositiveHom d x := sorry

/-- Projecting after including the positive-even part is the identity. -/
@[simp]
theorem evenToEvenPositive_evenPositiveToEven (x : A.evenPositivePart) :
    A.evenToEvenPositive (A.evenPositiveToEven x) = x := sorry

/-- The canonical inclusion of the positive-even part is injective. -/
theorem evenPositiveToEven_injective : Function.Injective A.evenPositiveToEven := sorry

/-- The degree equality underlying multiplication of two even homogeneous elements. -/
theorem evenMulDegree (i j : ℕ) : 2 * i + 2 * j = 2 * (i + j) := sorry

/-- The degree equality underlying multiplication by a positive even homogeneous element. -/
theorem evenMulPositiveDegree (i j : ℕ) :
    2 * i + 2 * (j + 1) = 2 * (i + j + 1) := sorry

/-- The degree equality underlying multiplication of two odd homogeneous elements. -/
theorem oddMulDegree (i j : ℕ) :
    (2 * i + 1) + (2 * j + 1) = 2 * (i + j + 1) := sorry

/-- The degree equality underlying multiplication of an even and an odd homogeneous element. -/
theorem evenMulOddDegree (i j : ℕ) :
    2 * i + (2 * j + 1) = 2 * (i + j) + 1 := sorry

/-- The homogeneous contribution to multiplication on the even part. -/
def evenMulTermMap (i j : ℕ) :
    A.piece (2 * i) →ₗ[R] A.piece (2 * j) →ₗ[R] A.evenPart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.evenHom (i + j)).comp <| A.pieceCast (evenMulDegree i j)

/-- Multiplication of two homogeneous even elements, included in the even part. -/
def evenMulTerm (i j : ℕ) (x : A.piece (2 * i)) (y : A.piece (2 * j)) : A.evenPart :=
  A.evenMulTermMap i j x y

/-- The homogeneous contribution of even-by-positive-even multiplication. -/
def evenMulPositiveTermMap (i j : ℕ) :
    A.piece (2 * i) →ₗ[R] A.piece (2 * (j + 1)) →ₗ[R] A.evenPositivePart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.evenPositiveHom (i + j)).comp <| A.pieceCast (evenMulPositiveDegree i j)

/-- Multiplication of homogeneous even and positive-even elements. -/
def evenMulPositiveTerm (i j : ℕ)
    (x : A.piece (2 * i)) (y : A.piece (2 * (j + 1))) : A.evenPositivePart :=
  A.evenMulPositiveTermMap i j x y

/-- The homogeneous contribution of odd-by-odd multiplication. -/
def oddMulTermMap (i j : ℕ) :
    A.piece (2 * i + 1) →ₗ[R] A.piece (2 * j + 1) →ₗ[R] A.evenPositivePart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.evenPositiveHom (i + j)).comp <| A.pieceCast (oddMulDegree i j)

/-- Multiplication of two homogeneous odd elements, included in the positive-even part. -/
def oddMulTerm (i j : ℕ)
    (x : A.piece (2 * i + 1)) (y : A.piece (2 * j + 1)) : A.evenPositivePart :=
  A.oddMulTermMap i j x y

/-- The homogeneous contribution of even-by-odd multiplication. -/
def evenMulOddTermMap (i j : ℕ) :
    A.piece (2 * i) →ₗ[R] A.piece (2 * j + 1) →ₗ[R] A.oddPart :=
  (DirectSum.gMulLHom R A.piece).compr₂ <|
    (A.oddHom (i + j)).comp <| A.pieceCast (evenMulOddDegree i j)

/-- Multiplication of homogeneous even and odd elements. -/
def evenMulOddTerm (i j : ℕ)
    (x : A.piece (2 * i)) (y : A.piece (2 * j + 1)) : A.oddPart :=
  A.evenMulOddTermMap i j x y

/-- Multiplication on the full even direct sum. -/
def evenMul : A.evenPart →ₗ[R] A.evenPart →ₗ[R] A.evenPart :=
  DirectSum.toModule R ℕ (A.evenPart →ₗ[R] A.evenPart) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i) →ₗ[R] A.evenPart) fun j ↦
      (A.evenMulTermMap i j).flip).flip

/-- Multiplication of the even part on the positive-even part. -/
def evenMulPositiveDirect :
    A.evenPart →ₗ[R] A.evenPositivePart →ₗ[R] A.evenPositivePart :=
  DirectSum.toModule R ℕ (A.evenPositivePart →ₗ[R] A.evenPositivePart) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i) →ₗ[R] A.evenPositivePart) fun j ↦
      (A.evenMulPositiveTermMap i j).flip).flip

/-- Multiplication of the even part on the odd part. -/
def evenMulOddDirect : A.evenPart →ₗ[R] A.oddPart →ₗ[R] A.oddPart :=
  DirectSum.toModule R ℕ (A.oddPart →ₗ[R] A.oddPart) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i) →ₗ[R] A.oddPart) fun j ↦
      (A.evenMulOddTermMap i j).flip).flip

/-- Multiplication of the odd part with itself, landing in the positive-even part. -/
def oddMulDirect : A.oddPart →ₗ[R] A.oddPart →ₗ[R] A.evenPositivePart :=
  DirectSum.toModule R ℕ (A.oddPart →ₗ[R] A.evenPositivePart) fun i ↦
    (DirectSum.toModule R ℕ (A.piece (2 * i + 1) →ₗ[R] A.evenPositivePart) fun j ↦
      (A.oddMulTermMap i j).flip).flip

/-- Multiplication of an even element with a positive-even element. -/
def evenMulPositive (x : A.evenPart) (y : A.evenPositivePart) : A.evenPositivePart :=
  A.evenMulPositiveDirect x y

/-- Multiplication of an even element with an odd element. -/
def evenMulOdd (x : A.evenPart) (y : A.oddPart) : A.oddPart :=
  A.evenMulOddDirect x y

/-- Multiplication of two odd elements. -/
def oddMul (x y : A.oddPart) : A.evenPositivePart :=
  A.oddMulDirect x y

/-- Multiplication by zero in the odd part vanishes. -/
@[simp]
theorem evenMulOdd_zero (x : A.evenPart) : A.evenMulOdd x 0 = 0 := sorry

/-- The unit of the even part, coming from homogeneous degree zero. -/
abbrev oneEven : A.evenPart :=
  A.evenHom 0 (GradedMonoid.GOne.one : A.piece 0)

/-- Natural powers in the even part using its canonical multiplication. -/
def evenPow : A.evenPart → ℕ → A.evenPart
  | _, 0 => A.oneEven
  | x, n + 1 => A.evenMul (evenPow x n) x

/-- The zeroth power in the even part is the graded unit. -/
@[simp]
theorem evenPow_zero (x : A.evenPart) : A.evenPow x 0 = A.oneEven := sorry

/-- The successor rule for powers in the even part. -/
@[simp]
theorem evenPow_succ (x : A.evenPart) (n : ℕ) :
    A.evenPow x (n + 1) = A.evenMul (A.evenPow x n) x := sorry

end NonnegGradedAlgebra
