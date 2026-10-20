/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.OfPredifferential
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.DividedPowers

/-!
# The predifferential for adjoining an odd variable

This file constructs the odd adjoining-variable differential on homogeneous coefficient
families.  Its computational core is independent of divided powers: for a positive degree `d`,
a family of base differentials `D`, and `f` in degree `d - 1`, it sends

`x T` to `D(x) T + (-1) ^ deg(x) (x * f)`.

The finite-support sum, exponent reindexing, degree casts, and Koszul sign are all explicit.
The second half specializes the construction to a divided-power chain algebra, proves the
derivation, divided-power, and square-zero laws propositionally, and assembles the canonical
odd cell and its universal lift.
-/

@[expose] public section

noncomputable section

open CategoryTheory ChainGradedAlgebra
open scoped DirectSum

universe u v

namespace NonnegGradedAlgebra.Adjoin.Odd.CoefficientDifferential

variable {R : Type u} [CommRing R]

/-- The exponent-one index in an output coefficient piece whenever its weight is admissible. -/
def oneIndex (d : ℕ+) (m : ℕ) (h : (d : ℕ) ≤ m) :
    {i : Fin 2 // (i : ℕ) * (d : ℕ) ≤ m} :=
  NonnegGradedAlgebra.Adjoin.Odd.oneIndexOfLE d h

/-- Extract the base coefficient from an exponent-zero monomial. -/
def constantCoefficient (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+) {m : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * (d : ℕ) ≤ m})
    (x : A.piece (m - (i : ℕ) * (d : ℕ))) (hi : (i : ℕ) = 0) : A.piece m :=
  A.pieceCast
    ((congrArg (fun q : ℕ ↦ m - q * (d : ℕ)) hi).trans <|
      (congrArg (fun q : ℕ ↦ m - q) (Nat.zero_mul (d : ℕ))).trans <|
        Nat.sub_zero m) x

/-- Extract the base coefficient multiplying `T` from an exponent-one monomial. -/
def variableCoefficient (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+) {m : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * (d : ℕ) ≤ m})
    (x : A.piece (m - (i : ℕ) * (d : ℕ))) (hi : (i : ℕ) ≠ 0) :
    A.piece (m - (d : ℕ)) :=
  A.pieceCast
    ((congrArg (fun q : Fin 2 ↦ m - (q : ℕ) * (d : ℕ))
      (Fin.eq_one_of_ne_zero i.1 fun h ↦ hi (congrArg Fin.val h))).trans <|
        congrArg (fun q : ℕ ↦ m - q) (Nat.one_mul (d : ℕ))) x

/-- The differential of a constant coefficient, inserted back at exponent zero. -/
def constantTerm (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (m : ℕ) (x : A.piece (m + 1)) : Piece A d m :=
  baseCoeff A d m <|
    A.pieceCast (Nat.add_one_sub_one m)
      (D ⟨m + 1, Nat.zero_lt_succ m⟩ x)

/-- The `D(x) T` summand in the differential of an exponent-one monomial. -/
def variableTerm (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (m : ℕ) (x : A.piece ((m + 1) - (d : ℕ))) : Piece A d m :=
  if h : (d : ℕ) ≤ m then
    DFinsupp.single (oneIndex d m h) <|
      A.pieceCast
        (((congrArg (fun q : ℕ ↦ q - 1) (Nat.succ_sub h)).trans <|
          Nat.add_one_sub_one (m - (d : ℕ))).trans <|
            congrArg (fun q : ℕ ↦ m - q) (Nat.one_mul (d : ℕ)).symm) <|
        D ⟨(m + 1) - (d : ℕ), tsub_pos_of_lt (Nat.lt_succ_of_le h)⟩ x
  else 0

/-- The signed attaching product `(-1) ^ deg(x) (x * f)`, reindexed to total degree `m`. -/
def attachingProduct (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ) (h : (d : ℕ) ≤ m + 1)
    (x : A.piece ((m + 1) - (d : ℕ))) : A.piece m :=
  (-1 : R) ^ ((m + 1) - (d : ℕ)) •
    A.pieceCast
      ((add_tsub_assoc_of_le (Nat.one_le_iff_ne_zero.mpr d.2.ne')
          ((m + 1) - (d : ℕ))).symm.trans <|
        (congrArg (fun q : ℕ ↦ q - 1) (Nat.sub_add_cancel h)).trans <|
          Nat.add_one_sub_one m) (GradedMonoid.GMul.mul x f)

/-- The signed attaching-product summand, inserted at exponent zero. -/
def attachingTerm (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ) (h : (d : ℕ) ≤ m + 1)
    (x : A.piece ((m + 1) - (d : ℕ))) : Piece A d m :=
  baseCoeff A d m (attachingProduct A d f m h x)

/-- The differential of one odd-variable coefficient monomial.  Exponent zero uses the base
differential; exponent one is exactly `D(x) T + (-1) ^ deg(x) (x * f)`. -/
def monomial (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * (d : ℕ) ≤ m + 1})
    (x : A.piece ((m + 1) - (i : ℕ) * (d : ℕ))) : Piece A d m :=
  if hi : (i : ℕ) = 0 then
    constantTerm A d D m (constantCoefficient A d i x hi)
  else
    variableTerm A d D m (variableCoefficient A d i x hi) +
      attachingTerm A d f m
        (Eq.mp
          (congrArg (fun q : ℕ ↦ q ≤ m + 1) <|
            (congrArg (fun q : Fin 2 ↦ (q : ℕ) * (d : ℕ))
              (Fin.eq_one_of_ne_zero i.1 fun h ↦ hi (congrArg Fin.val h))).trans <|
                Nat.one_mul (d : ℕ)) i.property)
        (variableCoefficient A d i x hi)

/-- Apply the odd coefficient differential by summing its explicit monomial formula over the
finite support. -/
def apply (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ) (z : Piece A d (m + 1)) : Piece A d m :=
  NonnegGradedAlgebra.Adjoin.Implementation.sum z fun i x ↦ monomial A d D f m i x

/-- The explicit coefficient differential preserves addition. -/
theorem apply_add (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ) (x y : Piece A d (m + 1)) :
    apply A d D f m (x + y) = apply A d D f m x + apply A d D f m y := sorry

/-- The explicit coefficient differential preserves scalar multiplication. -/
theorem apply_smul (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ) (r : R) (x : Piece A d (m + 1)) :
    apply A d D f m (r • x) = r • apply A d D f m x := sorry

/-- Tag 09PM: the degree-lowering linear map on odd-variable coefficient pieces. -/
@[stacks 09PM "explicit odd coefficient differential"]
def map (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ) : Piece A d (m + 1) →ₗ[R] Piece A d m where
  toFun := apply A d D f m
  map_add' := apply_add A d D f m
  map_smul' := apply_smul A d D f m

/-- The coefficient differential on a single monomial is the explicit monomial formula. -/
@[simp]
theorem map_single (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ+)
    (D : ∀ n : ℕ+, A.piece n →ₗ[R] A.piece ((n : ℕ) - 1))
    (f : A.piece ((d : ℕ) - 1)) (m : ℕ)
    (i : {i : Fin 2 // (i : ℕ) * (d : ℕ) ≤ m + 1})
    (x : A.piece ((m + 1) - (i : ℕ) * (d : ℕ))) :
    map A d D f m (DFinsupp.single i x) = monomial A d D f m i x := sorry

end NonnegGradedAlgebra.Adjoin.Odd.CoefficientDifferential

namespace DividedPowerChainAlgebra.Adjoin.Odd

variable {R : Type u} [CommRing R]

/-- The divided-power graded algebra obtained by adjoining an exterior variable in degree `d`. -/
def gradedAlgebra (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ)) : DividedPowerGradedAlgebra.{u, v} R :=
  NonnegGradedAlgebra.Adjoin.Odd.dpAlgebra A.toChainDGAlgebra.nonnegativePart d A.gamma hd

/-- The positive-degree differential family on the base nonnegative graded algebra. -/
def baseDifferential (A : DividedPowerChainAlgebra.{u, v} R) :
    ∀ n : ℕ+, A.toChainDGAlgebra.nonnegativePart.piece n →ₗ[R]
      A.toChainDGAlgebra.nonnegativePart.piece ((n : ℕ) - 1) :=
  fun n ↦ A.toChainDGAlgebra.nonnegativeDifferential n

/-- The explicit coefficient differential specialized to the differential and attaching element
of a divided-power chain algebra. -/
def coefficientDifferential (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (m : ℕ) :
    NonnegGradedAlgebra.Adjoin.Odd.Piece A.toChainDGAlgebra.nonnegativePart d (m + 1) →ₗ[R]
      NonnegGradedAlgebra.Adjoin.Odd.Piece A.toChainDGAlgebra.nonnegativePart d m :=
  NonnegGradedAlgebra.Adjoin.Odd.CoefficientDifferential.map
    A.toChainDGAlgebra.nonnegativePart d (baseDifferential A) f m

namespace CoefficientDifferential

/-- For a degree-one odd variable, the constant coefficient of the differential is the base
differential plus the signed attaching product of the variable coefficient. -/
@[stacks 0GZ6 "constant coefficient of the degree-one odd differential"]
theorem baseProjection_one (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (m : ℕ)
    (x : NonnegGradedAlgebra.Adjoin.Odd.Piece
      A.toChainDGAlgebra.nonnegativePart 1 (m + 1)) :
    NonnegGradedAlgebra.Adjoin.Odd.baseProjection
        A.toChainDGAlgebra.nonnegativePart 1 m
        (coefficientDifferential A (1 : ℕ+) f m x) =
      A.toChainDGAlgebra.nonnegativePart.pieceCast (Nat.add_one_sub_one m)
          (A.toChainDGAlgebra.nonnegativeDifferential
            ⟨m + 1, Nat.zero_lt_succ m⟩
            (NonnegGradedAlgebra.Adjoin.Odd.baseProjection
              A.toChainDGAlgebra.nonnegativePart 1 (m + 1) x)) +
        NonnegGradedAlgebra.Adjoin.Odd.CoefficientDifferential.attachingProduct
          A.toChainDGAlgebra.nonnegativePart (1 : ℕ+) f m
            (Nat.succ_le_succ (Nat.zero_le m))
            (NonnegGradedAlgebra.Adjoin.Odd.variableProjection
              A.toChainDGAlgebra.nonnegativePart 1
                (Nat.succ_le_succ (Nat.zero_le m)) x) := sorry

/-- For a degree-one odd variable, the variable coefficient of the differential is the base
differential of the preceding variable coefficient. -/
@[stacks 0GZ6 "variable coefficient of the degree-one odd differential"]
theorem variableProjection_one (A : DividedPowerChainAlgebra.{u, v} R)
    (f : A.toChainDGAlgebra.nonnegativePiece 0) (m : ℕ) (hm : 1 ≤ m)
    (x : NonnegGradedAlgebra.Adjoin.Odd.Piece
      A.toChainDGAlgebra.nonnegativePart 1 (m + 1)) :
    NonnegGradedAlgebra.Adjoin.Odd.variableProjection
        A.toChainDGAlgebra.nonnegativePart 1 hm
        (coefficientDifferential A (1 : ℕ+) f m x) =
      A.toChainDGAlgebra.nonnegativeDifferential
          ⟨m, lt_of_lt_of_le Nat.zero_lt_one hm⟩
          (NonnegGradedAlgebra.Adjoin.Odd.variableProjection
            A.toChainDGAlgebra.nonnegativePart 1
              (Nat.succ_le_succ (Nat.zero_le m)) x) := sorry

end CoefficientDifferential

/-- The positive natural-degree component of the odd adjoining-variable predifferential. -/
def positivePredifferentialMap (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (m : ℕ) :
    (gradedAlgebra A d hd).toChainGradedAlgebra.X (m + 1 : ℕ) →ₗ[R]
      (gradedAlgebra A d hd).toChainGradedAlgebra.X (((m + 1 : ℕ) : ℤ) + (-1)) :=
  ((gradedAlgebra A d hd).toChainGradedAlgebra.reindex
    (Int.add_neg_cancel_right (m : ℤ) 1).symm).comp (coefficientDifferential A d f m)

/-- The explicit degree-`-1` homogeneous map on the odd adjoining-variable algebra. -/
def predifferentialMap (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) :
    HomogeneousMap (gradedAlgebra A d hd).toChainGradedAlgebra (-1)
  | .ofNat 0 => 0
  | .ofNat (m + 1) => positivePredifferentialMap A d hd f m
  | .negSucc _ => 0

/-- The explicit odd coefficient map satisfies the graded Leibniz rule. -/
theorem predifferentialMap_mem (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) :
    predifferentialMap A d hd f ∈
      derivationSubmodule (gradedAlgebra A d hd).toChainGradedAlgebra (-1) := sorry

/-- The odd adjoining-variable coefficient map bundled as a graded predifferential. -/
def predifferential (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) :
    ChainGradedAlgebra.Predifferential (gradedAlgebra A d hd).toChainGradedAlgebra :=
  ⟨predifferentialMap A d hd f, predifferentialMap_mem A d hd f⟩

/-- The odd adjoining-variable predifferential preserves the transported divided powers. -/
theorem predifferential_preservesDP (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) :
    (gradedAlgebra A d hd).PreservesDP (predifferential A d hd f) := sorry

/-- Tag 0GZ4: the divided-power-compatible predifferential for adjoining an odd variable with
`dT = f`. -/
@[stacks 0GZ4 "odd adjoining-variable predifferential"]
def toGradedPredifferential (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) :
    (gradedAlgebra A d hd).Predifferential where
  toPredifferential := predifferential A d hd f
  preservesDP := predifferential_preservesDP A d hd f

/-- The odd adjoining-variable predifferential squares to zero when the attaching element is a
cycle. -/
theorem toGradedPredifferential_isSquareZero
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (toGradedPredifferential A d hd f).IsSquareZero := sorry

/-- Lemma 23.6.8 (09PM) (1): the explicit odd adjoining-variable predifferential assembled as a
divided-power chain algebra. -/
@[stacks 09PM "explicit odd adjoining-variable chain algebra"]
def chainAlgebra (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    DividedPowerChainAlgebra.{u, v} R :=
  (toGradedPredifferential A d hd f).toChainAlgebra
    (toGradedPredifferential_isSquareZero A d hd f hf)

/-- The assembled chain algebra has the canonical odd divided-power graded algebra underneath. -/
@[simp]
theorem chainAlgebra_toGradedAlgebra
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (chainAlgebra A d hd f hf).toGradedAlgebra = gradedAlgebra A d hd := sorry

/-- On positive coefficient degrees, the assembled chain differential is the explicit
coefficient differential. -/
@[simp]
theorem chainAlgebra_d_apply
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (m : ℕ)
    (x : NonnegGradedAlgebra.Adjoin.Odd.Piece
      A.toChainDGAlgebra.nonnegativePart d (m + 1)) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativeDifferential
        ⟨m + 1, Nat.zero_lt_succ m⟩ x =
      coefficientDifferential A d f m x := sorry

/-- The degreewise linear family underlying the canonical base inclusion. -/
def inclusionLinearMap
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    ∀ n : ℤ, A.toChainDGAlgebra.X n →ₗ[R]
      (chainAlgebra A d hd f hf).toChainDGAlgebra.X n
  | .ofNat m => NonnegGradedAlgebra.Adjoin.Odd.baseMap
      A.toChainDGAlgebra.nonnegativePart d m
  | .negSucc _ => 0

/-- The explicit base-inclusion maps commute with the chain differentials. -/
theorem inclusionLinearMap_comm
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    ModuleCat.ofHom (inclusionLinearMap A d hd f hf i) ≫
        (chainAlgebra A d hd f hf).toChainDGAlgebra.toChainComplex.d i j =
      A.toChainDGAlgebra.toChainComplex.d i j ≫
        ModuleCat.ofHom (inclusionLinearMap A d hd f hf j) := sorry

/-- The chain map underlying the canonical inclusion of the base algebra. -/
def inclusionChainMap
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    A.toChainDGAlgebra.toChainComplex ⟶
      (chainAlgebra A d hd f hf).toChainDGAlgebra.toChainComplex where
  f n := ModuleCat.ofHom (inclusionLinearMap A d hd f hf n)
  comm' := inclusionLinearMap_comm A d hd f hf

/-- The canonical inclusion preserves the homogeneous unit. -/
theorem inclusionChainMap_one
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (inclusionChainMap A d hd f hf).f 0 A.toChainDGAlgebra.one =
      (chainAlgebra A d hd f hf).toChainDGAlgebra.one := sorry

/-- The canonical inclusion preserves homogeneous multiplication. -/
theorem inclusionChainMap_mul
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (n m : ℤ) (x : A.toChainDGAlgebra.X n) (y : A.toChainDGAlgebra.X m) :
    (inclusionChainMap A d hd f hf).f (n + m) (A.toChainDGAlgebra.mul n m x y) =
      (chainAlgebra A d hd f hf).toChainDGAlgebra.mul n m
        ((inclusionChainMap A d hd f hf).f n x)
        ((inclusionChainMap A d hd f hf).f m y) := sorry

/-- The canonical base inclusion as a chain-DGA homomorphism. -/
def inclusionChainHom
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    ChainDGAlgebra.Hom A.toChainDGAlgebra (chainAlgebra A d hd f hf).toChainDGAlgebra where
  toChainMap := inclusionChainMap A d hd f hf
  map_one := inclusionChainMap_one A d hd f hf
  map_mul := inclusionChainMap_mul A d hd f hf

/-- The canonical base inclusion preserves divided powers. -/
theorem inclusionChainHom_map_gamma
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (n : ℕ) (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (inclusionChainHom A d hd f hf).nonnegativePart.evenMap (A.gamma n x) =
      (chainAlgebra A d hd f hf).gamma n
        ((inclusionChainHom A d hd f hf).nonnegativePart.evenPositiveMap x) := sorry

/-- The canonical inclusion of the base divided-power chain algebra. -/
def inclusion
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    A ⟶ chainAlgebra A d hd f hf where
  toChainHom := inclusionChainHom A d hd f hf
  map_gamma := inclusionChainHom_map_gamma A d hd f hf

/-- Forgetting divided powers from the canonical inclusion recovers its explicit chain-DGA
map. -/
@[simp]
theorem inclusion_toChainHom
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (inclusion A d hd f hf).toChainHom = inclusionChainHom A d hd f hf := sorry

/-- In every nonnegative degree, the canonical inclusion is the explicit constant-coefficient
map. -/
@[simp]
theorem inclusion_apply_ofNat
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (m : ℕ) (x : A.toChainDGAlgebra.nonnegativePiece m) :
    (inclusion A d hd f hf).toChainHom (m : ℤ) x =
      NonnegGradedAlgebra.Adjoin.Odd.baseMap
        A.toChainDGAlgebra.nonnegativePart d m x := sorry

/-- The canonical adjoined generator in degree `d`. -/
def generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePiece d :=
  NonnegGradedAlgebra.Adjoin.Odd.generator A.toChainDGAlgebra.nonnegativePart d

/-- The canonical generator satisfies `dT = f` after the base inclusion. -/
theorem differential_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativeDifferential d
        (generator A d hd f hf) =
      (inclusion A d hd f hf).toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f := sorry

/-- The divided-power graded lift determined by a base map and the image of the odd generator. -/
def gradedLift
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d) : gradedAlgebra A d hd ⟶ C.toGradedAlgebra :=
  NonnegGradedAlgebra.Adjoin.Odd.liftDP A.toChainDGAlgebra.nonnegativePart d A.gamma hd
    C.gamma g.toGradedHom x

/-- The degreewise linear family underlying the relative odd-cell lift. -/
def liftLinearMap
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d) :
    ∀ n : ℤ, (chainAlgebra A d hd f hf).toChainDGAlgebra.X n →ₗ[R]
      C.toChainDGAlgebra.X n
  | .ofNat m => (gradedLift A d hd g x).toGradedHom.map m
  | .negSucc _ => 0

/-- The relative lift maps commute with the differentials when the chosen generator image has
the prescribed differential. -/
theorem liftLinearMap_comm
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    ModuleCat.ofHom (liftLinearMap A d hd f hf g x i) ≫ C.toChainDGAlgebra.toChainComplex.d i j =
      (chainAlgebra A d hd f hf).toChainDGAlgebra.toChainComplex.d i j ≫
        ModuleCat.ofHom (liftLinearMap A d hd f hf g x j) := sorry

/-- The chain map underlying the relative odd-cell lift. -/
def liftChainMap
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.toChainComplex ⟶
      C.toChainDGAlgebra.toChainComplex where
  f n := ModuleCat.ofHom (liftLinearMap A d hd f hf g x n)
  comm' := liftLinearMap_comm A d hd f hf g x hx

/-- The relative odd-cell lift preserves the homogeneous unit. -/
theorem liftChainMap_one
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    (liftChainMap A d hd f hf g x hx).f 0
        (chainAlgebra A d hd f hf).toChainDGAlgebra.one = C.toChainDGAlgebra.one := sorry

/-- The relative odd-cell lift preserves homogeneous multiplication. -/
theorem liftChainMap_mul
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f)
    (n m : ℤ) (a : (chainAlgebra A d hd f hf).toChainDGAlgebra.X n)
    (b : (chainAlgebra A d hd f hf).toChainDGAlgebra.X m) :
    (liftChainMap A d hd f hf g x hx).f (n + m)
        ((chainAlgebra A d hd f hf).toChainDGAlgebra.mul n m a b) =
      C.toChainDGAlgebra.mul n m
        ((liftChainMap A d hd f hf g x hx).f n a)
        ((liftChainMap A d hd f hf g x hx).f m b) := sorry

/-- The relative odd-cell lift as a chain-DGA homomorphism. -/
def liftChainHom
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    ChainDGAlgebra.Hom (chainAlgebra A d hd f hf).toChainDGAlgebra C.toChainDGAlgebra where
  toChainMap := liftChainMap A d hd f hf g x hx
  map_one := liftChainMap_one A d hd f hf g x hx
  map_mul := liftChainMap_mul A d hd f hf g x hx

/-- The relative odd-cell chain map preserves divided powers. -/
theorem liftChainHom_map_gamma
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f)
    (n : ℕ)
    (a : (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (liftChainHom A d hd f hf g x hx).nonnegativePart.evenMap
        ((chainAlgebra A d hd f hf).gamma n a) =
      C.gamma n ((liftChainHom A d hd f hf g x hx).nonnegativePart.evenPositiveMap a) := sorry

/-- The explicit relative lift from the canonical odd cell. -/
def lift
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    chainAlgebra A d hd f hf ⟶ C where
  toChainHom := liftChainHom A d hd f hf g x hx
  map_gamma := liftChainHom_map_gamma A d hd f hf g x hx

/-- Forgetting divided powers from the canonical odd-cell lift recovers its explicit chain-DGA
map. -/
@[simp]
theorem lift_toChainHom
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    (lift A d hd f hf g x hx).toChainHom =
      liftChainHom A d hd f hf g x hx := sorry

/-- In every nonnegative degree, the canonical odd-cell lift is the graded lift determined by
the prescribed base map and generator image. -/
@[simp]
theorem lift_apply_ofNat
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f)
    (m : ℕ)
    (a : (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePiece m) :
    (lift A d hd f hf g x hx).toChainHom (m : ℤ) a =
      (gradedLift A d hd g x).toGradedHom.map m a := sorry

/-- The explicit relative lift restricts to the prescribed base map. -/
theorem inclusion_comp_lift
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    inclusion A d hd f hf ≫ lift A d hd f hf g x hx = g := sorry

/-- The explicit relative lift sends the adjoined generator to the chosen element. -/
theorem lift_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    (lift A d hd f hf g x hx).toChainHom d (generator A d hd f hf) = x := sorry

/-- Maps out of the canonical odd cell are determined by the base and generator values. -/
theorem hom_ext
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R}
    (g h : chainAlgebra A d hd f hf ⟶ C)
    (hbase : inclusion A d hd f hf ≫ g = inclusion A d hd f hf ≫ h)
    (hgenerator : g.toChainHom d (generator A d hd f hf) =
      h.toChainHom d (generator A d hd f hf)) : g = h := sorry

/-- The canonical odd adjoining-variable algebra with its relative cell mapping property. -/
@[stacks 09PM "canonical odd one-cell universal property"]
def cell
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    Cell A d f where
  attaching_isCycle := hf
  algebra := chainAlgebra A d hd f hf
  ι := inclusion A d hd f hf
  generator := generator A d hd f hf
  map_generator := differential_generator A d hd f hf
  lift := lift A d hd f hf
  lift_base := inclusion_comp_lift A d hd f hf
  lift_generator := lift_generator A d hd f hf
  hom_ext := hom_ext A d hd f hf

/-- The algebra carried by the canonical odd cell is the explicit adjoining-variable chain
algebra. -/
@[simp]
theorem cell_algebra
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).algebra = chainAlgebra A d hd f hf := sorry

/-- The base map carried by the canonical odd cell is the explicit inclusion. -/
@[simp]
theorem cell_ι
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).ι = inclusion A d hd f hf := sorry

/-- The distinguished element carried by the canonical odd cell is the explicit generator. -/
@[simp]
theorem cell_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (cell A d hd f hf).generator = generator A d hd f hf := sorry

/-- The universal lift carried by the canonical odd cell is the explicit coefficientwise lift. -/
@[simp]
theorem cell_lift
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece d)
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom (((d : ℕ) - 1 : ℕ) : ℤ) f) :
    (cell A d hd f hf).lift g x hx = lift A d hd f hf g x hx := sorry

/-- The degreewise identity coefficient presentation of the canonical odd cell. -/
def pieceEquiv
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (m : ℕ) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePiece m ≃ₗ[R]
      NonnegGradedAlgebra.Adjoin.Odd.Piece A.toChainDGAlgebra.nonnegativePart d m :=
  LinearEquiv.refl R _

/-- In coefficient coordinates, the canonical inclusion is the constant coefficient. -/
theorem pieceEquiv_base
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (m : ℕ) (x : A.toChainDGAlgebra.nonnegativePiece m) :
    pieceEquiv A d hd f hf m ((inclusion A d hd f hf).toChainHom m x) =
      DividedPowerChainAlgebra.Adjoin.Odd.baseCoeff
        A.toChainDGAlgebra.nonnegativePart d m x := sorry

/-- In coefficient coordinates, the canonical generator is the exponent-one vector. -/
theorem pieceEquiv_generator
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    pieceEquiv A d hd f hf d (generator A d hd f hf) =
      DividedPowerChainAlgebra.Adjoin.Odd.generatorCoeff
        A.toChainDGAlgebra.nonnegativePart d := sorry

/-- The even part of the canonical odd cell in parity coefficient coordinates. -/
def evenEquiv
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePart.evenPart ≃ₗ[R]
      NonnegGradedAlgebra.Adjoin.Odd.Coeffs A.toChainDGAlgebra.nonnegativePart :=
  NonnegGradedAlgebra.Adjoin.Odd.evenReindex A.toChainDGAlgebra.nonnegativePart d hd

/-- The positive even part of the canonical odd cell in parity coefficient coordinates. -/
def positiveEvenEquiv
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePart.evenPositivePart ≃ₗ[R]
      NonnegGradedAlgebra.Adjoin.Odd.PositiveCoeffs A.toChainDGAlgebra.nonnegativePart :=
  NonnegGradedAlgebra.Adjoin.Odd.positiveReindex A.toChainDGAlgebra.nonnegativePart d hd

/-- Divided powers on the canonical odd cell are the explicit parity coefficient formula. -/
theorem gamma_coeff
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f)
    (n : ℕ)
    (x : (chainAlgebra A d hd f hf).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    evenEquiv A d hd f hf ((chainAlgebra A d hd f hf).gamma n x) =
      NonnegGradedAlgebra.Adjoin.Odd.gamma A.toChainDGAlgebra.nonnegativePart A.gamma n
        (positiveEvenEquiv A d hd f hf x) := sorry

/-- Lemma 23.6.8 (09PM) (1): the canonical explicit odd one-cell extension. -/
@[stacks 09PM "canonical explicit odd one-cell extension"]
def extension
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    Extension A d f where
  toCell := cell A d hd f hf
  degree_odd := hd

/-- Forgetting the coefficient presentation from the canonical odd extension recovers its
canonical cell. -/
@[simp]
theorem extension_toCell
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (extension A d hd f hf).toCell = cell A d hd f hf := sorry

/-- The canonical explicit extension has the assembled coefficient chain algebra as its owner. -/
@[simp]
theorem extension_algebra
    (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+) (hd : Odd (d : ℕ))
    (f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) (hf : IsCycle A d f) :
    (extension A d hd f hf).algebra = chainAlgebra A d hd f hf := sorry

end DividedPowerChainAlgebra.Adjoin.Odd
