module

public import ReasLib.RingTheory.Algebra.Epicenter.Matrix
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated matrices for epicenter expressions

The row and column contractions in a `MatrixExpr` come from the base ring.
This leaf packages chosen base-ring matrices realizing those contractions;
the core epicenter and matrix-criterion leaves do not depend on this view.
-/

@[expose] public section

open Matrix

universe u v

namespace Algebra.Epicenter.MatrixExpr

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {g : S}

/-- Base-ring row and column matrices associated to a chosen finite matrix
expression. -/
@[stacks 04VZ "associated matrices for an epicenter expression"]
def IsAssociated (E : MatrixExpr (R := R) g)
    (U : Matrix (Fin 1) (Fin E.size) R)
    (V : Matrix (Fin E.size) (Fin 1) R) : Prop :=
  U.map (algebraMap R S) =
      replicateRow (Fin 1)
        (Matrix.vecMul E.left (E.coeff.map (algebraMap R S))) ∧
    V.map (algebraMap R S) =
      replicateCol (Fin 1)
        (Matrix.mulVec (E.coeff.map (algebraMap R S)) E.right)

/-- Chosen base-ring row and column matrices associated to a finite matrix
expression. -/
@[stacks 04VZ "associated matrix data"]
structure Associated (E : MatrixExpr (R := R) g) where
  /-- The base-ring row matrix. -/
  row : Matrix (Fin 1) (Fin E.size) R
  /-- The base-ring column matrix. -/
  column : Matrix (Fin E.size) (Fin 1) R
  /-- The chosen matrices realize the two contractions of `E`. -/
  isAssociated : E.IsAssociated row column

/-- Choose associated base-ring row and column matrices for a finite matrix
expression. -/
@[stacks 04VZ "chosen associated matrices"]
noncomputable def associated (E : MatrixExpr (R := R) g) : E.Associated where
  row _ j := Classical.choose (E.row j)
  column i _ := Classical.choose (E.column i)
  isAssociated := by
    constructor
    · ext i j
      simpa only [Matrix.map_apply, replicateRow_apply] using
        Classical.choose_spec (E.row j)
    · ext i j
      simpa only [Matrix.map_apply, replicateCol_apply] using
        Classical.choose_spec (E.column i)

/-- Every finite matrix expression has associated base-ring row and column
matrices. -/
@[stacks 04VZ "existence of associated matrices"]
theorem exists_associated (E : MatrixExpr (R := R) g) :
    ∃ U : Matrix (Fin 1) (Fin E.size) R,
      ∃ V : Matrix (Fin E.size) (Fin 1) R, E.IsAssociated U V :=
  ⟨E.associated.row, E.associated.column, E.associated.isAssociated⟩

end Algebra.Epicenter.MatrixExpr

namespace Algebra.Epicenter

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Every epicenter element admits a finite matrix expression together with
associated base-ring row and column matrices. -/
@[stacks 04VZ "associated matrices for an epicenter element"]
theorem exists_associated (g : Algebra.epicenter (R := R) (S := S)) :
    ∃ E : MatrixExpr (R := R) (g : S),
      ∃ U : Matrix (Fin 1) (Fin E.size) R,
        ∃ V : Matrix (Fin E.size) (Fin 1) R, E.IsAssociated U V := by
  rcases (mem_iff_hasMatrixExpr (R := R) (g : S)).mp g.property with ⟨E⟩
  exact ⟨E, E.associated.row, E.associated.column,
    E.associated.isAssociated⟩

end Algebra.Epicenter
