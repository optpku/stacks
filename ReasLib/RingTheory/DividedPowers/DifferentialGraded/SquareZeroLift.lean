/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Derivation.SquareZero
public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Semilinear
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation.Quotient
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.NonnegativeModel
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.OfPredifferential
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.ShiftedHomology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Predifferential
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.BaseChange
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Free
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Quotient
public import ReasLib.RingTheory.RingHom.SquareZero.Quotient

/-!
# Lifting divided-power differentials over principal square-zero extensions

A lift of a free divided-power chain algebra carries a divided-power-compatible
predifferential whose square need not vanish.  Its square is first divided by the chosen kernel
generator on the lifted algebra, producing a derivation on the source annihilator quotient.  The
canonical equivalence of scalar quotients then transports that derivation to the original algebra
modulo the descended annihilator.

The lift and all comparison maps are explicit data.  In particular, the obstruction on the
original quotient is not selected from an existence theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ChainGradedAlgebra
open RingHom.SquareZeroExtension

universe u v w

namespace DividedPowerChainAlgebra

variable {R' R : Type u} [CommRing R'] [CommRing R]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {generators : ℕ → Type v}

/-- The original differential descended to the quotient by the annihilator of a square-zero
kernel. -/
def annihilatorQuotientPredifferential (A : DividedPowerChainAlgebra.{u, w} R) :
    ChainGradedAlgebra.Predifferential
      (A.toGradedAlgebra.toChainGradedAlgebra.quotientByIdeal (kernelAnnihilator f)) :=
  ChainGradedAlgebra.Predifferential.quotientByIdeal
    A.toGradedPredifferential.toPredifferential (kernelAnnihilator f)

/-- The predifferential on the kernel-annihilator quotient is square-zero. -/
theorem annihilatorQuotientPredifferential_isSquareZero
    (A : DividedPowerChainAlgebra.{u, w} R) :
    ChainGradedAlgebra.Predifferential.IsSquareZero
      (A.annihilatorQuotientPredifferential (f := f)) := sorry

/-- The canonical chain DGA obtained by quotienting a divided-power chain algebra by the
annihilator of a square-zero kernel. -/
@[stacks 09PS "annihilator quotient chain DGA", stacks 09PT "annihilator quotient chain DGA"]
def annihilatorQuotient (A : DividedPowerChainAlgebra.{u, w} R) :
    ChainDGAlgebra.{u, w} (R ⧸ kernelAnnihilator f) :=
  A.toChainDGAlgebra.nonnegativeModel.quotientByIdeal (kernelAnnihilator f)

/-- The chain-graded algebra underlying `annihilatorQuotient` is the degreewise annihilator
quotient of the original divided-power graded algebra. -/
theorem annihilatorQuotient_toChainGradedAlgebra (A : DividedPowerChainAlgebra.{u, w} R) :
    (A.annihilatorQuotient (f := f)).toChainGradedAlgebra =
      A.toGradedAlgebra.toChainGradedAlgebra.quotientByIdeal
        (kernelAnnihilator f) := sorry

/-- A lift of a free divided-power chain algebra across a principal square-zero extension.

Besides the lifted predifferential, the structure records the base-change identification and its
induced comparison on annihilator quotients.  These comparisons are part of the reusable model,
so downstream obstruction constructions do not rebuild local scalar or quotient instances. -/
@[stacks 09PS "principal square-zero lift of a divided-power differential"]
structure SquareZeroLift (A : DividedPowerChainAlgebra.{u, w} R) (g : Generator f)
    (P : A.toGradedAlgebra.FreePresentation generators) where
  /-- The lifted divided-power graded algebra over the source ring. -/
  algebra : DividedPowerGradedAlgebra.{u, w} R'
  /-- The lifted free presentation on the same graded generator family. -/
  presentation : algebra.FreePresentation generators
  /-- The lifted divided-power-compatible predifferential. -/
  predifferential : algebra.Predifferential
  /-- The scalar-extension model reducing the lifted algebra along the square-zero map. -/
  reduction : algebra.BaseChangeAlong f
  /-- The reduction of the lifted algebra is identified with the original graded algebra. -/
  identify : reduction.target ≅ A.toGradedAlgebra
  /-- The reduction identification sends lifted generators to the original generators. -/
  map_generator (n : ℕ) (x : generators n) :
    reduction.mapPieceTo identify.hom n (presentation.generator n x) = P.generator n x
  /-- The lifted predifferential reduces to the original chain differential. -/
  map_d (i : ℤ) (x : algebra.toChainGradedAlgebra.X i) :
    reduction.mapChainPieceTo identify.hom (i + (-1))
        (predifferential.toPredifferential i x) =
      A.toGradedPredifferential.toPredifferential i
        (reduction.mapChainPieceTo identify.hom i x)
  /-- The square of the lifted predifferential is divisible by the chosen kernel generator. -/
  square_divisible :
    ChainGradedAlgebra.Derivation.IsDivisibleBy
      (DividedPowerGradedAlgebra.DPDerivation.square predifferential).toDerivation g
  /-- The source and target annihilator quotients are identified degreewise and multiplicatively
  over the canonical equivalence of scalar quotient rings. -/
  quotientComparison : ChainGradedAlgebra.SemilinearEquiv (sourceQuotientEquiv f)
    (algebra.toChainGradedAlgebra.quotientByIdeal (sourceKernelAnnihilator f))
    (A.toGradedAlgebra.toChainGradedAlgebra.quotientByIdeal (kernelAnnihilator f))
  /-- On every homogeneous representative, the quotient comparison is reduction followed by the
  target quotient map. -/
  quotientComparison_mk (i : ℤ) (x : algebra.toChainGradedAlgebra.X i) :
    quotientComparison.map i
        (ChainGradedAlgebra.IdealQuotient.mk algebra.toChainGradedAlgebra
          (sourceKernelAnnihilator f) i x) =
      ChainGradedAlgebra.IdealQuotient.mk A.toGradedAlgebra.toChainGradedAlgebra
        (kernelAnnihilator f) i (reduction.mapChainPieceTo identify.hom i x)
  /-- The quotient comparison carries the reduced lifted predifferential to the quotient of the
  original differential. -/
  quotientComparison_d :
    quotientComparison.conjugatePredifferential
        (ChainGradedAlgebra.Predifferential.quotientByIdeal
          predifferential.toPredifferential (sourceKernelAnnihilator f)) =
      A.annihilatorQuotientPredifferential
  /-- The quotient comparison carries source divided-power classes to the corresponding target
  classes under reduction. -/
  quotientComparison_gamma (n d : ℕ)
      (x : algebra.toGradedAlgebra.piece (2 * (d + 1))) :
    quotientComparison.map (2 * (n * (d + 1)) : ℕ)
        (algebra.quotientGammaPiece (sourceKernelAnnihilator f) n d x) =
      A.toGradedAlgebra.quotientGammaPiece (kernelAnnihilator f) n d
        (reduction.mapPieceTo identify.hom (2 * (d + 1)) x)

namespace SquareZeroLift

variable {A : DividedPowerChainAlgebra.{u, w} R} {g : Generator f}
variable {P : A.toGradedAlgebra.FreePresentation generators}

/-- The lifted chain-graded algebra modulo the source kernel annihilator. -/
abbrev sourceQuotientAlgebra (L : A.SquareZeroLift g P) :=
  L.algebra.toChainGradedAlgebra.quotientByIdeal (sourceKernelAnnihilator f)

/-- The lifted predifferential descended to the source annihilator quotient. -/
def sourcePredifferential (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Predifferential L.sourceQuotientAlgebra :=
  ChainGradedAlgebra.Predifferential.quotientByIdeal
    L.predifferential.toPredifferential (sourceKernelAnnihilator f)

/-- Divide the square of the lifted predifferential by the chosen kernel generator on the source
annihilator quotient. -/
@[stacks 09PS "source square obstruction after division by the kernel generator"]
def sourceObstruction (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Derivation L.sourceQuotientAlgebra (-2) :=
  L.square_divisible.divide

/-- Multiplication by the kernel generator recovers the square of the lifted predifferential on
every homogeneous representative. -/
@[stacks 09PS "recovery of the lifted differential square"]
theorem sourceObstruction_recovery (L : A.SquareZeroLift g P) (i : ℤ)
    (x : L.algebra.toChainGradedAlgebra.X i) :
    (((g.quotientEquivRange (L.algebra.toChainGradedAlgebra.X (i + (-2)))
          (L.square_divisible.exact (i + (-2))))
        (L.sourceObstruction i
          (ChainGradedAlgebra.IdealQuotient.mk L.algebra.toChainGradedAlgebra
            (sourceKernelAnnihilator f) i x)) :
          LinearMap.range
            (g.moduleMul (L.algebra.toChainGradedAlgebra.X (i + (-2))))) :
        L.algebra.toChainGradedAlgebra.X (i + (-2))) =
      (DividedPowerGradedAlgebra.DPDerivation.square L.predifferential).toDerivation i x := sorry

/-- The source obstruction is closed under the quotient predifferential. -/
theorem sourceObstruction_isClosed (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Derivation.IsClosed L.sourceObstruction
      L.sourcePredifferential := sorry

/-- The source obstruction satisfies the divided-power derivation formula on quotient classes. -/
theorem sourceObstruction_preservesDP (L : A.SquareZeroLift g P) :
    L.algebra.PreservesDPModulo (sourceKernelAnnihilator f) L.sourceObstruction := sorry

/-- The quotient comparison transports the source quotient predifferential to the target quotient
predifferential. -/
theorem conjugate_sourcePredifferential (L : A.SquareZeroLift g P) :
    L.quotientComparison.conjugatePredifferential L.sourcePredifferential =
      A.annihilatorQuotientPredifferential := sorry

/-- The underlying target obstruction derivation, obtained by semilinear conjugation from the
divided source square. -/
def obstructionDerivation (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Derivation
      (A.toGradedAlgebra.toChainGradedAlgebra.quotientByIdeal
        (kernelAnnihilator f)) (-2) :=
  L.quotientComparison.conjugateDerivation L.sourceObstruction

/-- The target obstruction acts on comparison images by applying the source obstruction and then
the forward quotient comparison. -/
@[simp]
theorem obstructionDerivation_map (L : A.SquareZeroLift g P) (i : ℤ)
    (x : L.sourceQuotientAlgebra.X i) :
    L.obstructionDerivation i (L.quotientComparison.map i x) =
      L.quotientComparison.map (i + (-2)) (L.sourceObstruction i x) := sorry

/-- The transported obstruction satisfies the divided-power derivation formula on the original
annihilator quotient. -/
theorem obstructionDerivation_preservesDP (L : A.SquareZeroLift g P) :
    A.toGradedAlgebra.PreservesDPModulo (kernelAnnihilator f)
      L.obstructionDerivation := sorry

/-- The degree-`-2` divided-power obstruction derivation on the original algebra modulo the
annihilator of the square-zero kernel. -/
@[stacks 09PS "obstruction derivation on the original annihilator quotient"]
def obstruction (L : A.SquareZeroLift g P) :
    DividedPowerGradedAlgebra.IdealQuotient.DPDerivation A.toGradedAlgebra
      (kernelAnnihilator f) A.annihilatorQuotientPredifferential (-2) where
  toDerivation := L.obstructionDerivation
  isClosed := L.quotientComparison.isClosed_conjugate_of_eq
    L.sourceObstruction_isClosed L.conjugate_sourcePredifferential
  preservesDP := L.obstructionDerivation_preservesDP

/-- The underlying derivation of the obstruction is semilinear conjugation of the divided source
square. -/
@[simp]
theorem obstruction_toDerivation (L : A.SquareZeroLift g P) :
    L.obstruction.toDerivation = L.obstructionDerivation := sorry

/-- The obstruction evaluates on comparison images by transporting the divided source square. -/
@[simp]
theorem obstruction_map (L : A.SquareZeroLift g P) (i : ℤ)
    (x : L.sourceQuotientAlgebra.X i) :
    L.obstruction i (L.quotientComparison.map i x) =
      L.quotientComparison.map (i + (-2)) (L.sourceObstruction i x) := sorry

/-- The homogeneous-map data of the obstruction on the chain DGA quotient.  Its components are
definitionally the components of the obstruction on the underlying annihilator quotient, so no
equality transport enters the computational data. -/
@[stacks 09PS "chain obstruction homogeneous map"]
def chainObstructionMap (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.HomogeneousMap
      (A.annihilatorQuotient (f := f)).toChainGradedAlgebra (-2) :=
  ChainGradedAlgebra.Derivation.toHomogeneousMap L.obstruction.toDerivation

/-- The homogeneous obstruction map satisfies the Leibniz rule on the chain DGA quotient. -/
@[stacks 09PS "chain obstruction Leibniz law"]
theorem chainObstructionMap_satisfiesLeibniz (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.SatisfiesLeibniz
      (A.annihilatorQuotient (f := f)).toChainGradedAlgebra (-2)
        L.chainObstructionMap := sorry

/-- The obstruction derivation on the chain-graded algebra underlying the quotient chain DGA. -/
@[stacks 09PS "chain obstruction derivation"]
def chainObstruction (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Derivation
      (A.annihilatorQuotient (f := f)).toChainGradedAlgebra (-2) :=
  ⟨L.chainObstructionMap, L.chainObstructionMap_satisfiesLeibniz⟩

/-- Forgetting the Leibniz law from the chain obstruction recovers its explicit homogeneous
map. -/
@[simp, stacks 09PS "chain obstruction underlying map"]
theorem chainObstruction_toHomogeneousMap (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Derivation.toHomogeneousMap L.chainObstruction =
      L.chainObstructionMap := sorry

/-- The chain obstruction evaluates by the transported divided-power obstruction in every
degree. -/
@[simp, stacks 09PS "chain obstruction evaluation"]
theorem chainObstruction_apply (L : A.SquareZeroLift g P) (i : ℤ)
    (x : (A.annihilatorQuotient (f := f)).toChainGradedAlgebra.X i) :
    L.chainObstruction i x = L.obstruction i x := sorry

/-- The transported obstruction is closed under the quotient chain differential. -/
@[stacks 09PS "chain obstruction closedness"]
theorem chainObstruction_isClosed (L : A.SquareZeroLift g P) :
    ChainGradedAlgebra.Derivation.IsClosed L.chainObstruction
      (A.annihilatorQuotient (f := f)).predifferential := sorry

/-- Applying a degree-`-2` map in degree two lands in degree zero. -/
@[stacks 09PS "degree of the square-zero obstruction"]
theorem obstructionHomologyDegree : (2 : ℤ) + (-2) = 0 := sorry

/-- The map from second to zeroth homology induced by the square-zero lifting obstruction. -/
@[stacks 09PT "obstruction map from second to zeroth homology"]
noncomputable def obstructionHomologyMap (L : A.SquareZeroLift g P) :
    (A.annihilatorQuotient (f := f)).homology 2 →ₗ[R ⧸ kernelAnnihilator f]
      (A.annihilatorQuotient (f := f)).homology 0 :=
  ChainGradedAlgebra.Derivation.homologyMapTo L.chainObstruction
    L.chainObstruction_isClosed (add_neg_cancel (2 : ℤ))

/-- On cycle classes, `obstructionHomologyMap` is represented by the obstruction derivation. -/
theorem obstructionHomologyMap_homologyπ (L : A.SquareZeroLift g P)
    (x : (A.annihilatorQuotient (f := f)).cycles 2) :
    L.obstructionHomologyMap
        ((A.annihilatorQuotient (f := f)).homologyπ 2 x) =
      (A.annihilatorQuotient (f := f)).homologyπ 0
        (ChainGradedAlgebra.Derivation.cyclesMapTo L.chainObstruction
          L.chainObstruction_isClosed obstructionHomologyDegree x) := sorry

/-- A finite free divided-power chain algebra admits a compatible lift across a principal
square-zero extension. -/
theorem nonempty_of_finite (A : DividedPowerChainAlgebra.{u, w} R) (g : Generator f)
    (P : A.toGradedAlgebra.FreePresentation generators)
    (h_finite : ∀ n : ℕ, Finite (generators n)) :
    Nonempty (A.SquareZeroLift g P) := sorry

/-- Lemma 23.7.1 (Tag 09PS): a divided-power polynomial chain algebra with finitely many
generators in each degree admits a degree-`-2` derivation on its quotient by the annihilator of a
principal square-zero kernel.  The witness is tied to an explicit compatible lift. -/
@[stacks 09PS "Lemma 23.7.1"]
theorem exists_obstruction_of_finite (A : DividedPowerChainAlgebra.{u, w} R) (g : Generator f)
    (P : A.toGradedAlgebra.FreePresentation generators)
    (h_finite : ∀ n : ℕ, Finite (generators n)) :
    ∃ (L : A.SquareZeroLift g P)
      (θ : ChainGradedAlgebra.Derivation
        (A.toGradedAlgebra.toChainGradedAlgebra.quotientByIdeal
          (kernelAnnihilator f)) (-2)),
      θ = L.obstruction.toDerivation := sorry

end SquareZeroLift

end DividedPowerChainAlgebra
