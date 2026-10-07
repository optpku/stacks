module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import ReasLib.RingTheory.GradedAlgebra.FiniteType
public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
public import ReasLib.RingTheory.Polynomial.Numerical.Closure
public import Mathlib.RingTheory.GradedAlgebra.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck classes of graded pieces

The graded pieces of a finite graded module define a function with values in the Grothendieck
group of finite modules over the degree-zero subalgebra. For a Noetherian graded algebra,
generation in degree one makes this class function a numerical polynomial.
-/

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory.ModuleCat.K0

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

include 𝒜 ℳ

/-
API design: `gradedPieceClass` is the base data owner.  It uses the existing `finiteClass` carrier,
the shared degree-zero module structure, and canonical finite-piece infrastructure; no `Data`
wrapper or caller-facing `letI` is exposed.  `gradedPieceClass_of_isNoetherian` is the one derived data owner
for a Noetherian ambient algebra; degree-one hypotheses appear only in the numerical-polynomial
theorem where they contribute mathematical content.
-/

/-- The `K'_0(S₀)`-valued class function of an internally graded module. -/
@[stacks 00K1 "graded-piece Grothendieck class function"]
noncomputable def gradedPieceClass [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] :
    ℤ → finite (𝒜 0) :=
  fun n ↦ letI := GradedModule.finitePiece 𝒜 ℳ n; finiteClass (𝒜 0) (ℳ n)

/-- Evaluation of `gradedPieceClass` is the finite-module class of the corresponding piece. -/
@[simp, stacks 00K1 "graded-piece Grothendieck class evaluation"]
theorem gradedPieceClass_apply [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (n : ℤ) [Module.Finite (𝒜 0) (ℳ n)] :
    gradedPieceClass 𝒜 ℳ n = finiteClass (𝒜 0) (ℳ n) := sorry

/-
API design: the periodic-polynomial chapter result has only Noetherianity, not a chosen
degree-one span.  This derived owner uses the generic Noetherian-to-finite-type bridge and keeps
that derivation internal, so consumers never reconstruct a finite-type instance.
-/

/-- The graded-piece class function of a Noetherian graded algebra and finite graded module. -/
@[stacks 02CD "Noetherian graded-piece class function"]
noncomputable def gradedPieceClass_of_isNoetherian [IsNoetherianRing S]
    [Module.Finite S M] : ℤ → finite (𝒜 0) :=
  letI : Algebra.FiniteType (𝒜 0) S :=
    GradedAlgebra.finiteType_of_isNoetherian 𝒜
  gradedPieceClass 𝒜 ℳ

/-- Degree-one generation makes the graded-piece class function a numerical polynomial. -/
@[stacks 00K1 "graded-piece numerical polynomial"]
theorem gradedPieceClass_isNumericalPolynomial [IsNoetherianRing S]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (hgen : Ideal.span (𝒜 1 : Set S) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    IsNumericalPolynomial (gradedPieceClass 𝒜 ℳ) := sorry

/-- A degree-one spanning hypothesis makes the canonical Noetherian graded-piece class function
numerical-polynomial. -/
@[stacks 00K1 "Noetherian graded-piece numerical polynomial"]
theorem gradedPieceClass_of_isNoetherian_isNumericalPolynomial [IsNoetherianRing S]
    [Module.Finite S M]
    (hgen : Ideal.span (𝒜 1 : Set S) = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    IsNumericalPolynomial (gradedPieceClass_of_isNoetherian 𝒜 ℳ) := sorry

end CategoryTheory.ModuleCat.K0
