module

public import ReasLib.RingTheory.Algebra.Epicenter
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite matrix criterion for the epicenter

`MatrixExpr g` bundles the complete finite witness.  Its proposition-valued
existence wrapper is equivalent to epicenter membership, so downstream code
may either consume the chosen matrices or use the subalgebra closure API.
-/

@[expose] public section

open Matrix
open scoped TensorProduct

universe u v

namespace Algebra.Epicenter

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A chosen finite matrix expression for `g` whose row and column
contractions lie in the image of the base ring. -/
@[stacks 04VY "finite epicenter matrix expression"]
structure MatrixExpr (g : S) where
  /-- The size of the expression. -/
  size : ℕ
  /-- The row vector over the algebra. -/
  left : Fin size → S
  /-- The column vector over the algebra. -/
  right : Fin size → S
  /-- The coefficient matrix over the base ring. -/
  coeff : Matrix (Fin size) (Fin size) R
  /-- The matrix expression evaluates to `g`. -/
  value : g = dotProduct
    (Matrix.vecMul left (coeff.map (algebraMap R S))) right
  /-- Every row contraction is a scalar from the base ring. -/
  row : ∀ j, Matrix.vecMul left (coeff.map (algebraMap R S)) j ∈
    Set.range (algebraMap R S)
  /-- Every column contraction is a scalar from the base ring. -/
  column : ∀ i, Matrix.mulVec (coeff.map (algebraMap R S)) right i ∈
    Set.range (algebraMap R S)

/-- An element admits some finite epicenter matrix expression. -/
@[stacks 04VY "existence of a finite epicenter matrix expression"]
def HasMatrixExpr (g : S) : Prop :=
  Nonempty (MatrixExpr (R := R) g)

/-- The finite matrix condition is equivalent to equality of the two
canonical tensors attached to `g`. -/
@[stacks 04VY]
theorem hasMatrixExpr_iff_tmul (g : S) :
    HasMatrixExpr (R := R) g ↔
      g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := sorry

/-- Epicenter membership is equivalent to admitting a finite matrix
expression over the base ring. -/
@[stacks 04VY "epicenter finite matrix criterion"]
theorem mem_iff_hasMatrixExpr (g : S) :
    g ∈ Algebra.epicenter (R := R) (S := S) ↔ HasMatrixExpr (R := R) g := by
  simpa only [Algebra.mem_epicenter] using
    (hasMatrixExpr_iff_tmul (R := R) g).symm

namespace MatrixExpr

/-- A chosen finite matrix expression certifies epicenter membership. -/
@[stacks 04VY "matrix expression gives epicenter membership"]
theorem mem {g : S} (E : MatrixExpr (R := R) g) :
    g ∈ Algebra.epicenter (R := R) (S := S) :=
  (mem_iff_hasMatrixExpr (R := R) g).mpr ⟨E⟩

end MatrixExpr

/-- Scalars from the base ring admit a finite matrix expression. -/
@[stacks 04VY "scalar finite matrix expression"]
theorem hasMatrixExpr_algebraMap (r : R) :
    HasMatrixExpr (R := R) (algebraMap R S r) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    ((Algebra.epicenter (R := R) (S := S)).algebraMap_mem r)

namespace HasMatrixExpr

/-- Zero admits a finite matrix expression. -/
@[stacks 04VY "zero finite matrix expression"]
theorem zero : HasMatrixExpr (R := R) (0 : S) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    (Algebra.epicenter (R := R) (S := S)).zero_mem

/-- One admits a finite matrix expression. -/
@[stacks 04VY "one finite matrix expression"]
theorem one : HasMatrixExpr (R := R) (1 : S) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    (Algebra.epicenter (R := R) (S := S)).one_mem

/-- Matrix expressions are closed under addition. -/
@[stacks 04VY "addition of finite matrix expressions"]
theorem add {x y : S} (hx : HasMatrixExpr (R := R) x)
    (hy : HasMatrixExpr (R := R) y) :
    HasMatrixExpr (R := R) (x + y) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    ((Algebra.epicenter (R := R) (S := S)).add_mem
      ((mem_iff_hasMatrixExpr (R := R) x).mpr hx)
      ((mem_iff_hasMatrixExpr (R := R) y).mpr hy))

/-- Matrix expressions are closed under multiplication. -/
@[stacks 04VY "multiplication of finite matrix expressions"]
theorem mul {x y : S} (hx : HasMatrixExpr (R := R) x)
    (hy : HasMatrixExpr (R := R) y) :
    HasMatrixExpr (R := R) (x * y) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    ((Algebra.epicenter (R := R) (S := S)).mul_mem
      ((mem_iff_hasMatrixExpr (R := R) x).mpr hx)
      ((mem_iff_hasMatrixExpr (R := R) y).mpr hy))

/-- Matrix expressions are closed under negation. -/
@[stacks 04VY "negation of finite matrix expressions"]
theorem neg {x : S} (hx : HasMatrixExpr (R := R) x) :
    HasMatrixExpr (R := R) (-x) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    ((Algebra.epicenter (R := R) (S := S)).neg_mem
      ((mem_iff_hasMatrixExpr (R := R) x).mpr hx))

/-- Matrix expressions are closed under subtraction. -/
@[stacks 04VY "subtraction of finite matrix expressions"]
theorem sub {x y : S} (hx : HasMatrixExpr (R := R) x)
    (hy : HasMatrixExpr (R := R) y) :
    HasMatrixExpr (R := R) (x - y) :=
  (mem_iff_hasMatrixExpr (R := R) _).mp
    ((Algebra.epicenter (R := R) (S := S)).sub_mem
      ((mem_iff_hasMatrixExpr (R := R) x).mpr hx)
      ((mem_iff_hasMatrixExpr (R := R) y).mpr hy))

end HasMatrixExpr

end Algebra.Epicenter
