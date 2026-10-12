/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra.Functor
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra.Representative
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra

/-!
# Divided powers on homology

This file constructs the descent of compatible divided powers along a surjective morphism from a
positive-acyclic chain DGA. The target is the canonical graded algebra on Mathlib homology modules,
and the induction predicate records the representative formula for every chain-level lift.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

/-- The nonnegative graded algebra on homology, obtained by forgetting to a strict chain DGA and
then applying the canonical strict-DGA homology functor. -/
@[stacks 09PK "graded homology functor"]
noncomputable def homology (R : Type u) [CommRing R] :
    DividedPowerChainAlgebra.{u, v} R ⥤ NonnegGradedAlgebra.{u, v} R :=
  forgetStrict R ⋙ ChainDGAlgebra.Strict.homology R

/-- The object part of the homology functor is the canonical nonnegative homology algebra. -/
@[simp] theorem homology_obj (A : DividedPowerChainAlgebra.{u, v} R) :
    (homology R).obj A = A.toChainDGAlgebra.homologyNonnegativePart := sorry

/-- The map part of the homology functor is the canonical graded homology homomorphism. -/
@[simp] theorem homology_map {A B : DividedPowerChainAlgebra.{u, v} R} (f : A ⟶ B) :
    (homology R).map f = f.toChainHom.homologyHom := sorry

end DividedPowerChainAlgebra

namespace DividedPowerChainAlgebra.Hom

variable {R : Type u} [CommRing R]
variable {A B : DividedPowerChainAlgebra.{u, v} R}

/-- A normalized chain-level lift in degree `n` of a target homology class through a
degreewise-surjective divided-power chain-DGA morphism. -/
noncomputable def homologyLiftPiece (f : Hom A B) (hf : f.Surjective) (n : ℕ)
    (x : B.toChainDGAlgebra.homologyPiece n) :
    A.toChainDGAlgebra.nonnegativePiece n :=
  Function.surjInv (hf n)
      (B.toChainDGAlgebra.iCycles n
        (B.toChainDGAlgebra.selectedHomologyCycle n x)) -
    Function.surjInv (hf n)
      (B.toChainDGAlgebra.iCycles n
        (B.toChainDGAlgebra.selectedHomologyCycle n 0))

/-- Mapping a selected chain-level lift to the target gives the normalized selected cycle. -/
theorem map_homologyLiftPiece (f : Hom A B) (hf : f.Surjective) (n : ℕ)
    (x : B.toChainDGAlgebra.homologyPiece n) :
    f.toChainHom.toChainMap.f n (f.homologyLiftPiece hf n x) =
      B.toChainDGAlgebra.iCycles n
        (B.toChainDGAlgebra.selectedHomologyCycle n x) := sorry

/-- The selected chain-level lift of the zero homology class is zero. -/
@[simp] theorem homologyLiftPiece_zero
    (f : Hom A B) (hf : f.Surjective) (n : ℕ) :
    f.homologyLiftPiece hf n 0 = 0 := sorry

/-- Lift every homogeneous component of the positive-even homology direct sum to the source
chain algebra. -/
noncomputable def homologyEvenPositiveLift (f : Hom A B) (hf : f.Surjective) :
    B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart →
      A.toChainDGAlgebra.nonnegativePart.evenPositivePart :=
  fun x ↦ DFinsupp.mapRange
    (fun d y ↦ f.homologyLiftPiece hf (2 * (d + 1)) y)
    (fun d ↦ f.homologyLiftPiece_zero hf (2 * (d + 1))) x

/-- The target even chain value obtained by lifting a homology input, applying the source
chain-level divided power, and mapping back along `f`. -/
noncomputable def homologyGammaChainValue (f : Hom A B) (hf : f.Surjective) (n : ℕ) :
    B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart →
      B.toChainDGAlgebra.nonnegativePart.evenPart :=
  fun x ↦
    f.toChainHom.nonnegativePart.evenMap <|
      A.gamma n (f.homologyEvenPositiveLift hf x)

/-- Every homogeneous component of `homologyGammaChainValue` is a target cycle. -/
theorem homologyGammaChainValue_isCycle
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) (d : ℕ) :
    ((forget₂ (ModuleCat.{v} R) Ab).map
      (B.toChainDGAlgebra.toChainComplex.sc (2 * d : ℤ)).g)
        (f.homologyGammaChainValue hf n x d) = 0 := sorry

/-- The explicit total divided-power operation on target homology: lift to the source, apply
the source chain-level divided power, map to the target, and take componentwise cycle classes. -/
noncomputable def homologyGamma
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ) :
    B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart →
      B.toChainDGAlgebra.homologyNonnegativePart.evenPart :=
  fun x ↦ B.toChainDGAlgebra.homologyEvenClassOfCycles
    (f.homologyGammaChainValue hf n x)
    (f.homologyGammaChainValue_isCycle hA hf n x)

/-- The target positive-even chain value obtained from the positive-index source divided power. -/
noncomputable def homologyGammaPosChainValue
    (f : Hom A B) (hf : f.Surjective) (n : ℕ+) :
    B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart →
      B.toChainDGAlgebra.nonnegativePart.evenPositivePart :=
  fun x ↦
    f.toChainHom.nonnegativePart.evenPositiveMap <|
      A.gamma.gammaPos n (f.homologyEvenPositiveLift hf x)

/-- Every homogeneous component of `homologyGammaPosChainValue` is a target cycle. -/
theorem homologyGammaPosChainValue_isCycle
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ+)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) (d : ℕ) :
    ((forget₂ (ModuleCat.{v} R) Ab).map
      (B.toChainDGAlgebra.toChainComplex.sc (2 * (d + 1) : ℤ)).g)
        (f.homologyGammaPosChainValue hf n x d) = 0 := sorry

/-- The explicit positive-index divided-power operation on target homology, retaining its
positive-even codomain. -/
noncomputable def homologyGammaPos
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ+) :
    B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart →
      B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart :=
  fun x ↦ B.toChainDGAlgebra.homologyEvenPositiveClassOfCycles
    (f.homologyGammaPosChainValue hf n x)
    (f.homologyGammaPosChainValue_isCycle hA hf n x)

/-- The explicit total and positive-index homology operations agree after inclusion. -/
theorem homologyGamma_eq_homologyGammaPos
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ+)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.homologyGamma hA hf n x =
      B.toChainDGAlgebra.homologyNonnegativePart.evenPositiveToEven
        (f.homologyGammaPos hA hf n x) := sorry

/-- The explicit homology divided power of a homogeneous class has the expected degree. -/
theorem homologyGamma_degree
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n d : ℕ)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.piece (2 * (d + 1))) :
    ∃ y : B.toChainDGAlgebra.homologyNonnegativePart.piece
        (2 * (n * (d + 1))),
      f.homologyGamma hA hf n
          (B.toChainDGAlgebra.homologyNonnegativePart.evenPositiveHom d x) =
        B.toChainDGAlgebra.homologyNonnegativePart.evenHom (n * (d + 1)) y := sorry

/-- The first explicit homology divided power is the positive-even inclusion. -/
theorem homologyGamma_one
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.homologyGamma hA hf 1 x =
      B.toChainDGAlgebra.homologyNonnegativePart.evenPositiveToEven x := sorry

/-- The zeroth explicit homology divided power is the graded unit. -/
theorem homologyGamma_zero
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.homologyGamma hA hf 0 x =
      B.toChainDGAlgebra.homologyNonnegativePart.oneEven := sorry

/-- Multiplication of explicit homology divided powers uses the binomial coefficient. -/
theorem homologyGamma_mul
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n m : ℕ)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    B.toChainDGAlgebra.homologyNonnegativePart.evenMul
        (f.homologyGamma hA hf n x) (f.homologyGamma hA hf m x) =
      Nat.choose (n + m) n • f.homologyGamma hA hf (n + m) x := sorry

/-- Explicit homology divided powers satisfy the even-factor multiplication law. -/
theorem homologyGamma_evenMul
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPart)
    (y : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.homologyGamma hA hf n
        (B.toChainDGAlgebra.homologyNonnegativePart.evenMulPositive x y) =
      B.toChainDGAlgebra.homologyNonnegativePart.evenMul
        (B.toChainDGAlgebra.homologyNonnegativePart.evenPow x n)
        (f.homologyGamma hA hf n y) := sorry

/-- Higher explicit homology divided powers vanish on products of homogeneous odd classes. -/
theorem homologyGamma_oddMul
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) {n : ℕ} (hn : 1 < n) (i j : ℕ)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.piece (2 * i + 1))
    (y : B.toChainDGAlgebra.homologyNonnegativePart.piece (2 * j + 1)) :
    f.homologyGamma hA hf n
        (B.toChainDGAlgebra.homologyNonnegativePart.oddMulTerm i j x y) = 0 := sorry

/-- Explicit homology divided powers turn sums into antidiagonal convolutions. -/
theorem homologyGamma_add
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ)
    (x y : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.homologyGamma hA hf n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦
        B.toChainDGAlgebra.homologyNonnegativePart.evenMul
          (f.homologyGamma hA hf ij.1 x)
          (f.homologyGamma hA hf ij.2 y) := sorry

/-- Iterated explicit homology divided powers use the canonical composition coefficient. -/
theorem homologyGamma_comp
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) (n : ℕ) (m : ℕ+)
    (x : B.toChainDGAlgebra.homologyNonnegativePart.evenPositivePart) :
    f.homologyGamma hA hf n (f.homologyGammaPos hA hf m x) =
      Nat.uniformBell n m • f.homologyGamma hA hf (n * (m : ℕ)) x := sorry

/-- Lemma 23.6.6 (Tag 09PK), canonical datum: the explicit divided powers induced on target
homology by a surjective map from a positive-acyclic divided-power chain algebra. -/
@[stacks 09PK "canonical induced divided powers on homology"]
noncomputable def dividedPowersOnHomology
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart where
  gamma := f.homologyGamma hA hf
  gammaPos := f.homologyGammaPos hA hf
  gamma_eq_gammaPos := f.homologyGamma_eq_homologyGammaPos hA hf
  gamma_degree := f.homologyGamma_degree hA hf
  gamma_one := f.homologyGamma_one hA hf
  gamma_zero := f.homologyGamma_zero hA hf
  gamma_mul := f.homologyGamma_mul hA hf
  gamma_evenMul := f.homologyGamma_evenMul hA hf
  gamma_oddMul := f.homologyGamma_oddMul hA hf
  gamma_add := f.homologyGamma_add hA hf
  gamma_comp := f.homologyGamma_comp hA hf

/-- A divided-power structure on `H(B)` is induced by `f : A ⟶ B` when every positive-even
homology class can be computed by lifting a cycle to `A`, applying the chain-level divided power,
and taking its image class in `B`. Requiring the formula for every lift records independence of
all representative choices. -/
def IsInducedOnHomology (f : Hom A B)
    (gammaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart) : Prop :=
  ∀ (n d : ℕ) (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℕ))
    (y : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))),
    f.toChainHom.toChainMap.f (2 * (d + 1)) y = B.toChainDGAlgebra.iCycles _ x →
      ∃ w : B.toChainDGAlgebra.cycles (2 * (n * (d + 1)) : ℕ),
        B.toChainDGAlgebra.iCycles _ w =
            f.toChainHom.toChainMap.f (2 * (n * (d + 1)))
              (A.gamma.gammaPiece n d y) ∧
          gammaH n
              (B.toChainDGAlgebra.homologyNonnegativePart.evenPositiveHom d
                (B.toChainDGAlgebra.homologyπ _ x)) =
            B.toChainDGAlgebra.homologyNonnegativePart.evenHom (n * (d + 1))
              (B.toChainDGAlgebra.homologyπ _ w)

/-- The explicit divided-power datum satisfies the representative formula characterizing the
structure induced by `f`. -/
theorem dividedPowersOnHomology_isInduced
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) :
    f.IsInducedOnHomology (f.dividedPowersOnHomology hA hf) := sorry

/-- The induced-structure predicate exposes the class formula for any chosen chain-level lift. -/
theorem IsInducedOnHomology.exists_cycleRepresentative
    {f : Hom A B}
    {gammaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (h : f.IsInducedOnHomology gammaH)
    (n d : ℕ) (x : B.toChainDGAlgebra.cycles (2 * (d + 1) : ℕ))
    (y : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1)))
    (hy : f.toChainHom.toChainMap.f (2 * (d + 1)) y =
      B.toChainDGAlgebra.iCycles _ x) :
    ∃ w : B.toChainDGAlgebra.cycles (2 * (n * (d + 1)) : ℕ),
      B.toChainDGAlgebra.iCycles _ w =
          f.toChainHom.toChainMap.f (2 * (n * (d + 1)))
            (A.gamma.gammaPiece n d y) ∧
        gammaH n
            (B.toChainDGAlgebra.homologyNonnegativePart.evenPositiveHom d
              (B.toChainDGAlgebra.homologyπ _ x)) =
          B.toChainDGAlgebra.homologyNonnegativePart.evenHom (n * (d + 1))
            (B.toChainDGAlgebra.homologyπ _ w) := sorry

/-- The existence-and-uniqueness form of the canonical `09PK` divided-power datum on `H(B)`. -/
theorem existsUnique_dividedPowersOnHomology
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) :
    ∃! gammaH : NonnegGradedAlgebra.DividedPowers
        B.toChainDGAlgebra.homologyNonnegativePart,
      f.IsInducedOnHomology gammaH := sorry

/-- Every divided-power structure satisfying the induced representative formula is the explicit
canonical structure `dividedPowersOnHomology`. -/
theorem eq_dividedPowersOnHomology
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective)
    {gammaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hgamma : f.IsInducedOnHomology gammaH) :
    gammaH = f.dividedPowersOnHomology hA hf := sorry

/-- Under the hypotheses of `09PK`, an induced divided-power structure exists on `H(B)`. -/
theorem exists_dividedPowersOnHomology
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective) :
    ∃ gammaH : NonnegGradedAlgebra.DividedPowers
        B.toChainDGAlgebra.homologyNonnegativePart,
      f.IsInducedOnHomology gammaH := sorry

/-- The divided-power structure induced on homology by a fixed surjective positive-acyclic source
is unique. -/
theorem dividedPowersOnHomology_unique
    (f : Hom A B) (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (hf : f.Surjective)
    {gammaH deltaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart}
    (hgamma : f.IsInducedOnHomology gammaH)
    (hdelta : f.IsInducedOnHomology deltaH) :
    gammaH = deltaH := sorry

end DividedPowerChainAlgebra.Hom
