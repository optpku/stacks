module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Predifferential

/-!
# Chain DGAs from square-zero predifferentials

This file gives the inverse construction to the canonical predifferential of a
chain differential graded algebra.  A square-zero predifferential on a
chain-graded algebra first determines an explicit `ChainComplex.of`; the
graded multiplication and unit then assemble into a chain DGA.
-/

@[expose] public section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra.Predifferential

variable {A : ChainGradedAlgebra.{u, v} R}

/-- The adjacent-degree component used to build the chain complex of a predifferential. -/
def differentialComponent (d : Predifferential A) (n : ℤ) :
    A.X (n + 1) ⟶ A.X n :=
  ModuleCat.ofHom <|
    (A.reindex (Int.add_neg_cancel_right n 1)).comp
      (ChainGradedAlgebra.Derivation.toHomogeneousMap d (n + 1))

/-- The adjacent-degree component evaluates as the original predifferential followed by
degree reindexing. -/
@[simp]
theorem differentialComponent_apply (d : Predifferential A) (n : ℤ)
    (x : A.X (n + 1)) :
    differentialComponent d n x =
      A.reindex (Int.add_neg_cancel_right n 1) (d (n + 1) x) := sorry

/-- Square-zero of the predifferential gives the adjacent differential-square relation. -/
theorem differentialComponent_sq (d : Predifferential A) (hd : IsSquareZero d)
    (n : ℤ) :
    differentialComponent d (n + 1) ≫ differentialComponent d n = 0 := sorry

/-- The chain complex determined by a square-zero predifferential. -/
def toChainComplex (d : Predifferential A) (hd : IsSquareZero d) :
    ChainComplex (ModuleCat.{v} R) ℤ :=
  ChainComplex.of A.X (differentialComponent d) (differentialComponent_sq d hd)

/-- The components of the chain complex constructed from a predifferential are the original
graded components. -/
@[simp]
theorem toChainComplex_X (d : Predifferential A) (hd : IsSquareZero d) (n : ℤ) :
    (toChainComplex d hd).X n = A.X n := sorry

/-- The adjacent differential in the constructed chain complex is
`differentialComponent`. -/
@[simp]
theorem toChainComplex_d (d : Predifferential A) (hd : IsSquareZero d) (n : ℤ) :
    (toChainComplex d hd).d (n + 1) n = differentialComponent d n := sorry

/-- The chain-complex differential induced by a predifferential satisfies the chain Leibniz
rule for the original graded multiplication. -/
theorem toChainComplex_leibniz (d : Predifferential A) (hd : IsSquareZero d)
    (n m : ℤ) (a : A.X n) (b : A.X m) :
    (toChainComplex d hd).d (n + m) (n + m - 1) (A.mul n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
          (ChainDGAlgebra.leftLeibnizIndex n m))
        (A.mul (n - 1) m ((toChainComplex d hd).d n (n - 1) a) b) +
      n.negOnePow •
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
            (ChainDGAlgebra.rightLeibnizIndex n m))
          (A.mul n (m - 1) a ((toChainComplex d hd).d m (m - 1) b)) := sorry

/-- A square-zero predifferential on a chain-graded algebra, assembled explicitly as a chain
differential graded algebra. -/
@[stacks 09PR "infrastructure: chain DGA associated to a square-zero predifferential"]
def toChainDGAlgebra (d : Predifferential A) (hd : IsSquareZero d) :
    ChainDGAlgebra.{u, v} R where
  toChainComplex := toChainComplex d hd
  mul := A.mul
  one := A.one
  mul_assoc := A.mul_assoc
  one_mul := A.one_mul
  mul_one := A.mul_one
  leibniz := toChainComplex_leibniz d hd

/-- The chain complex underlying `toChainDGAlgebra` is the explicitly constructed chain
complex. -/
@[simp]
theorem toChainDGAlgebra_toChainComplex (d : Predifferential A) (hd : IsSquareZero d) :
    (toChainDGAlgebra d hd).toChainComplex = toChainComplex d hd := sorry

/-- The degree-`n` component of the reconstructed chain DGA is the original graded component. -/
@[simp]
theorem toChainDGAlgebra_X (d : Predifferential A) (hd : IsSquareZero d) (n : ℤ) :
    (toChainDGAlgebra d hd).X n = A.X n := sorry

/-- The reconstructed chain-DGA differential acts as the original predifferential. -/
@[simp]
theorem toChainDGAlgebra_d_apply (d : Predifferential A) (hd : IsSquareZero d)
    (n : ℤ) (x : A.X n) :
    (toChainDGAlgebra d hd).d n x = d n x := sorry

/-- Forgetting the reconstructed chain DGA back to a chain-graded algebra recovers the original
algebra. -/
@[simp]
theorem toChainDGAlgebra_toChainGradedAlgebra
    (d : Predifferential A) (hd : IsSquareZero d) :
    (toChainDGAlgebra d hd).toChainGradedAlgebra = A := sorry

/-- The canonical predifferential of the reconstructed chain DGA is the original
predifferential. -/
@[simp]
theorem toChainDGAlgebra_predifferential
    (d : Predifferential A) (hd : IsSquareZero d) :
    (toChainDGAlgebra d hd).predifferential = d := sorry

/-- The predifferential round trip agrees pointwise on every homogeneous component. -/
@[simp]
theorem toChainDGAlgebra_predifferential_apply
    (d : Predifferential A) (hd : IsSquareZero d) (n : ℤ) (x : A.X n) :
    (toChainDGAlgebra d hd).predifferential n x = d n x := sorry

end ChainGradedAlgebra.Predifferential
