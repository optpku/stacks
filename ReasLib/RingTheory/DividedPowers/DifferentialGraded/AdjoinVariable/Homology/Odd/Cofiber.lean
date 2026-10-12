/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.Homotopy.CofiberShortComplex
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.ChainHomology
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.Bundled
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Homology.Odd.Cycle
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Model.Odd
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# The cofiber model of a degree-one odd cell

Adjoining an odd variable `T` in degree one with `d T = f` is the homotopy cofiber of
right multiplication by `f`.  The comparison is explicit in every integer degree: positive
degrees use the two coefficient projections with the chain-shift sign, degree zero uses the
low-degree constant-coefficient equivalence, and negative degrees use nonnegative support.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Odd.Extension

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {f : A.toChainDGAlgebra.nonnegativePiece 0}

/-- The homotopy cofiber of the attaching chain map of a degree-one odd cell. -/
abbrev cofiber (X : Odd.Extension A (1 : ℕ+) f) :
    ChainComplex (ModuleCat.{v} R) ℤ :=
  HomologicalComplex.homotopyCofiber X.attachingMap

namespace Cofiber

/-- Successive natural degrees are related by the chain-complex shape. -/
theorem succ_rel (m : ℕ) :
    (down ℤ).Rel ((Nat.succ m : ℕ) : ℤ) (m : ℤ) := sorry

/-- Degrees zero and negative one are related by the chain-complex shape. -/
theorem zero_rel : (down ℤ).Rel 0 (-1) := sorry

/-- Degree zero lies below the degree-one odd variable. -/
theorem zero_lt_one : 0 < (1 : ℕ) := sorry

/-- Negative one is a negative integer degree. -/
theorem neg_one_lt_zero : (-1 : ℤ) < 0 := sorry

/-- Every `Int.negSucc` degree is negative. -/
theorem negSucc_lt_zero (m : ℕ) : Int.negSucc m < 0 := sorry

/-- The index equality used by the degree-minus-one homology shift. -/
theorem shift_index (n : ℤ) : (-1 : ℤ) + n = n - 1 := sorry

/-- Every integer degree is related to the preceding degree in a chain complex. -/
theorem degree_rel (n : ℤ) : (down ℤ).Rel n (n - 1) := sorry

/-- The signed variable coefficient occurring in the cofiber projection of a degree-one odd
cell. -/
@[stacks 0GZ6 "signed variable coefficient of a degree-one odd cell"]
def signedVariableCoefficient (X : Odd.Extension A (1 : ℕ+) f) (m : ℕ) :
    X.algebra.toChainDGAlgebra.nonnegativePiece (Nat.succ m) →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece m :=
  (LinearEquiv.smulOfUnit ((-1 : Rˣ) ^ m) :
      A.toChainDGAlgebra.nonnegativePiece m ≃ₗ[R]
        A.toChainDGAlgebra.nonnegativePiece m).toLinearMap.comp
    (X.variableCoefficient (Nat.succ_le_succ (Nat.zero_le m)))

/-- The sign correction on the variable coefficient in positive degree `m + 1`. -/
def signEquiv (m : ℕ) :
    (A.toChainDGAlgebra.nonnegativePiece m ×
        A.toChainDGAlgebra.nonnegativePiece (Nat.succ m)) ≃ₗ[R]
      (A.toChainDGAlgebra.nonnegativePiece m ×
        A.toChainDGAlgebra.nonnegativePiece (Nat.succ m)) :=
  (LinearEquiv.smulOfUnit ((-1 : Rˣ) ^ m) :
      A.toChainDGAlgebra.nonnegativePiece m ≃ₗ[R]
        A.toChainDGAlgebra.nonnegativePiece m).prodCongr
    (LinearEquiv.refl R
      (A.toChainDGAlgebra.nonnegativePiece (Nat.succ m)))

/-- In a positive degree, the coefficient presentation identifies the odd cell with the
corresponding term of the attaching-map homotopy cofiber. -/
def positiveIso (X : Odd.Extension A (1 : ℕ+) f) (m : ℕ) :
    X.standardModel.algebra.toChainDGAlgebra.X ((Nat.succ m : ℕ) : ℤ) ≅
      X.cofiber.X ((Nat.succ m : ℕ) : ℤ) :=
  (Odd.pieceEquiv A 1 X.degree_odd f X.attaching_isCycle (Nat.succ m)).toModuleIso ≪≫
    (NonnegGradedAlgebra.Adjoin.Odd.splitEquiv
      A.toChainDGAlgebra.nonnegativePart 1
        (Nat.succ_le_succ (Nat.zero_le m))).toModuleIso ≪≫
    (LinearEquiv.prodComm R _ _).toModuleIso ≪≫
    (signEquiv (A := A) m).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd
      (A.toChainDGAlgebra.X (m : ℤ))
      (A.toChainDGAlgebra.X ((Nat.succ m : ℕ) : ℤ))).symm ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod X.attachingMap
      ((Nat.succ m : ℕ) : ℤ) (m : ℤ) (succ_rel m)).symm

/-- In degree zero, only the constant coefficient remains and the negative cofiber summand is
canonically zero. -/
def zeroIso (X : Odd.Extension A (1 : ℕ+) f) :
    X.standardModel.algebra.toChainDGAlgebra.X 0 ≅ X.cofiber.X 0 :=
  (Odd.pieceEquiv A 1 X.degree_odd f X.attaching_isCycle 0).toModuleIso ≪≫
    (NonnegGradedAlgebra.Adjoin.Odd.baseEquivOfLT
      A.toChainDGAlgebra.nonnegativePart 1 zero_lt_one).toModuleIso ≪≫
    isoZeroBiprod
      (A.toChainDGAlgebra.isZero_X_of_neg (-1) neg_one_lt_zero) ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      X.attachingMap 0 (-1) zero_rel).symm

/-- The attaching-map homotopy cofiber vanishes in every negative degree. -/
theorem cofiber_isZero_of_neg (X : Odd.Extension A (1 : ℕ+) f)
    (n : ℤ) (hn : n < 0) : IsZero (X.cofiber.X n) := sorry

/-- In a negative degree, nonnegative support gives the canonical comparison between the two
zero terms. -/
def negativeIso (X : Odd.Extension A (1 : ℕ+) f) (m : ℕ) :
    X.standardModel.algebra.toChainDGAlgebra.X (Int.negSucc m) ≅
      X.cofiber.X (Int.negSucc m) :=
  (X.standardModel.algebra.toChainDGAlgebra.isZero_X_of_neg
      (Int.negSucc m) (negSucc_lt_zero m)).isoZero ≪≫
    (cofiber_isZero_of_neg X (Int.negSucc m) (negSucc_lt_zero m)).isoZero.symm

/-- The explicit degreewise comparison from the standard odd-cell model to the homotopy cofiber
of the original cell's attaching map. -/
def modelIsoApp (X : Odd.Extension A (1 : ℕ+) f) :
    (n : ℤ) → X.standardModel.algebra.toChainDGAlgebra.X n ≅ X.cofiber.X n
  | .ofNat 0 => zeroIso X
  | .ofNat (Nat.succ m) => positiveIso X m
  | .negSucc m => negativeIso X m

/-- The standard-model coefficient comparison commutes with chain differentials. This follows
from the explicit odd coefficient differential, not from an arbitrary presentation equivalence. -/
theorem modelIsoApp_comm (X : Odd.Extension A (1 : ℕ+) f) (i j : ℤ)
    (hij : (down ℤ).Rel i j) :
    (modelIsoApp X i).hom ≫ X.cofiber.d i j =
      X.standardModel.algebra.toChainDGAlgebra.toChainComplex.d i j ≫
        (modelIsoApp X j).hom := sorry

/-- The standard explicit odd-cell model is the homotopy cofiber of the original cell's attaching
map. -/
def modelIso (X : Odd.Extension A (1 : ℕ+) f) :
    X.standardModel.algebra.toChainDGAlgebra.toChainComplex ≅ X.cofiber :=
  HomologicalComplex.Hom.isoOfComponents (modelIsoApp X) (modelIsoApp_comm X)

end Cofiber

/-- Lemma 23.12.3 (Tag 0GZ6): a degree-one odd cell is canonically the homotopy cofiber of
right multiplication by its attaching element. The explicit coefficient calculation is made on
the standard model and transported along the canonical cell comparison. -/
@[stacks 0GZ6 "degree-one odd cell as an attaching-map homotopy cofiber"]
def cofiberIso (X : Odd.Extension A (1 : ℕ+) f) :
    X.algebra.toChainDGAlgebra.toChainComplex ≅ X.cofiber :=
  Cell.Comparison.chainIso X.toCell X.standardModel.toCell ≪≫ Cofiber.modelIso X

/-- The degree-`n` component of the canonical cofiber comparison. -/
def cofiberIsoApp (X : Odd.Extension A (1 : ℕ+) f) (n : ℤ) :
    X.algebra.toChainDGAlgebra.X n ≅ X.cofiber.X n :=
  (HomologicalComplex.eval (ModuleCat.{v} R) (down ℤ) n).mapIso X.cofiberIso

/-- The canonical degreewise cofiber comparison commutes with chain differentials. -/
theorem cofiberIsoApp_comm (X : Odd.Extension A (1 : ℕ+) f) (i j : ℤ)
    (hij : (down ℤ).Rel i j) :
    (cofiberIsoApp X i).hom ≫ X.cofiber.d i j =
      X.algebra.toChainDGAlgebra.toChainComplex.d i j ≫
        (cofiberIsoApp X j).hom := sorry

/-- Under the cofiber comparison, the base inclusion is the canonical inclusion into the
homotopy cofiber. -/
theorem inclusion_comp_cofiberIso_hom (X : Odd.Extension A (1 : ℕ+) f) :
    X.toCell.ι.toChainHom.toChainMap ≫ X.cofiberIso.hom =
      ChainComplex.homotopyCofiber.inclusion X.attachingMap := sorry

/-- The canonical projection from a degree-one odd cell to the shifted base complex. -/
def projection (X : Odd.Extension A (1 : ℕ+) f) :
    X.algebra.toChainDGAlgebra.toChainComplex ⟶
      A.toChainDGAlgebra.toChainComplex⟦(-1 : ℤ)⟧ :=
  X.cofiberIso.hom ≫ ChainComplex.homotopyCofiber.projection X.attachingMap

/-- In successor natural degree, the odd-cell projection is the signed canonical variable
coefficient. -/
@[stacks 0GZ6 "degree-one odd-cell projection coefficient formula"]
theorem projection_succ (X : Odd.Extension A (1 : ℕ+) f) (m : ℕ) :
    X.projection.f ((Nat.succ m : ℕ) : ℤ) ≫
        (ChainComplex.Shift.MinusOne.succNatXIso
          A.toChainDGAlgebra.toChainComplex m).hom =
      ModuleCat.ofHom (Cofiber.signedVariableCoefficient X m) := sorry

namespace Comparison

/-- Canonical cell comparison intertwines the projections of any two degree-one odd-cell
presentations. -/
@[stacks 0GZ6 "model independence of the degree-one odd-cell projection"]
theorem projection (X Y : Odd.Extension A (1 : ℕ+) f) :
    (Cell.Comparison.chainIso X.toCell Y.toCell).hom ≫ Y.projection =
      X.projection := sorry

end Comparison

/-- The base inclusion followed by the canonical odd-cell projection is zero. -/
theorem inclusion_comp_projection (X : Odd.Extension A (1 : ℕ+) f) :
    X.toCell.ι.toChainHom.toChainMap ≫ X.projection = 0 := sorry

/-- The canonical short complex associated to a degree-one odd cell. -/
@[stacks 0GZ6 "degree-one odd-cell short complex"]
def shortComplex (X : Odd.Extension A (1 : ℕ+) f) :
    ShortComplex (ChainComplex (ModuleCat.{v} R) ℤ) :=
  ShortComplex.mk X.toCell.ι.toChainHom.toChainMap X.projection
    X.inclusion_comp_projection

namespace Comparison

/-- The first square comparing the canonical short complexes of two odd-cell presentations
commutes. -/
theorem shortComplex_comm₁₂ (X Y : Odd.Extension A (1 : ℕ+) f) :
    (Iso.refl A.toChainDGAlgebra.toChainComplex).hom ≫ Y.shortComplex.f =
      X.shortComplex.f ≫ (Cell.Comparison.chainIso X.toCell Y.toCell).hom := sorry

/-- The second square comparing the canonical short complexes of two odd-cell presentations
commutes. -/
theorem shortComplex_comm₂₃ (X Y : Odd.Extension A (1 : ℕ+) f) :
    (Cell.Comparison.chainIso X.toCell Y.toCell).hom ≫ Y.shortComplex.g =
      X.shortComplex.g ≫
        (Iso.refl (A.toChainDGAlgebra.toChainComplex⟦(-1 : ℤ)⟧)).hom := sorry

/-- The canonical short complex of a degree-one odd cell is independent of its chosen cell
presentation. -/
@[stacks 0GZ6 "model independence of the degree-one odd-cell short complex"]
def shortComplexIso (X Y : Odd.Extension A (1 : ℕ+) f) :
    X.shortComplex ≅ Y.shortComplex :=
  ShortComplex.isoMk (Iso.refl _) (Cell.Comparison.chainIso X.toCell Y.toCell) (Iso.refl _)
    (shortComplex_comm₁₂ X Y) (shortComplex_comm₂₃ X Y)

end Comparison

/-- The first square defining the comparison with the generic cofiber short complex commutes. -/
theorem shortComplexIso_comm₁₂ (X : Odd.Extension A (1 : ℕ+) f) :
    (Iso.refl A.toChainDGAlgebra.toChainComplex).hom ≫
        (ChainComplex.homotopyCofiber.shortComplex X.attachingMap).f =
      X.shortComplex.f ≫ X.cofiberIso.hom := sorry

/-- The second square defining the comparison with the generic cofiber short complex commutes. -/
theorem shortComplexIso_comm₂₃ (X : Odd.Extension A (1 : ℕ+) f) :
    X.cofiberIso.hom ≫
        (ChainComplex.homotopyCofiber.shortComplex X.attachingMap).g =
      X.shortComplex.g ≫
        (Iso.refl (A.toChainDGAlgebra.toChainComplex⟦(-1 : ℤ)⟧)).hom := sorry

/-- The odd-cell short complex is canonically isomorphic to the generic homotopy-cofiber short
complex. -/
def shortComplexIso (X : Odd.Extension A (1 : ℕ+) f) :
    X.shortComplex ≅ ChainComplex.homotopyCofiber.shortComplex X.attachingMap :=
  ShortComplex.isoMk (Iso.refl _) X.cofiberIso (Iso.refl _)
    X.shortComplexIso_comm₁₂ X.shortComplexIso_comm₂₃

/-- The canonical odd-cell short complex is short exact. -/
@[stacks 0GZ6 "degree-one odd-cell short exact sequence"]
theorem shortExact (X : Odd.Extension A (1 : ℕ+) f) :
    X.shortComplex.ShortExact := sorry

/-- The boundary of the odd-cell homology sequence is the homology map of the shifted attaching
endomorphism. -/
@[stacks 0GZ6 "degree-one odd-cell boundary map"]
theorem boundary_eq_shiftedAttachingMap (X : Odd.Extension A (1 : ℕ+) f) (n : ℤ) :
    X.shortExact.δ n (n - 1) (Cofiber.degree_rel n) =
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (down ℤ) 0).shiftMap
        (X.attachingMap⟦(-1 : ℤ)⟧') n (n - 1) (Cofiber.shift_index n) := sorry

end DividedPowerChainAlgebra.Adjoin.Odd.Extension
