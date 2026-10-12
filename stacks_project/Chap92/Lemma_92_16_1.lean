/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_16_1_Comparison
public import stacks_project.Chap92.Lemma_92_16_1_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Deformations of ring maps and the cotangent complex

In the square-zero situation of 92.16.0.1, solutions are governed by
Ext⁽n⁾_B(L_{B/A}, N): a canonical class ξ in Ext⁽2⁾ vanishes iff a solution
exists; isomorphism classes of solutions are principal homogeneous under
Ext⁽1⁾; automorphisms of a given solution fitting the diagram are Ext⁽0⁾.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory
open Algebra.CotangentComplex
open RingHom.SquareZeroExtension
open scoped DerivedExt

namespace RingHom.SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (c : KernelModule π →ₗ[A] N)

/-- Lemma 92.16.1 (1) In the situation above we have: there is a canonical element
ξ ∈ Ext⁽2⁾_B(L_{B/A}, N) whose vanishing is a sufficient and necessary condition
for the existence of a solution to (92.16.0.1). -/
@[stacks 08SP]
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction π B c = 0 ↔ Nonempty (@Solution A' A _ _ B _ _ π _ N _ _ _ c _) :=
  sorry

/-- Lemma 92.16.1 (2) If there exists a solution, then the set of isomorphism classes
of solutions is principal homogeneous under Ext⁽1⁾_B(L_{B/A}, N). Existence is the
basepoint S0; the acting group is Ext⁽1⁾ of Algebra.CotangentComplex.derived A B. -/
@[stacks 08SP]
def isoClassDerivedEquiv (S0 : @Solution A' A _ _ B _ _ π _ N _ _ _ c _) :
    Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) ≃ IsoClass π B c :=
  (extOneNaiveDerivedEquiv A B N).toEquiv.symm.trans (isoClassEquiv S0)

/-- The based chart sends a derived Ext¹ class to the translate of the basepoint. -/
theorem isoClassDerivedEquiv_apply (S0 : @Solution A' A _ _ B _ _ π _ N _ _ _ c _)
    (ξ : Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) :
    isoClassDerivedEquiv π B c S0 ξ =
      isoClassEquiv S0 ((extOneNaiveDerivedEquiv A B N).symm ξ) :=
  sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassDerivedEquiv_zero (S0 : @Solution A' A _ _ B _ _ π _ N _ _ _ c _) :
    isoClassDerivedEquiv π B c S0 0 = isoClassMk S0 :=
  sorry

/-- The inverse chart is the naive torsor subtraction, transported along
`extOneNaiveDerivedEquiv`. -/
theorem isoClassDerivedEquiv_symm_apply (S0 : @Solution A' A _ _ B _ _ π _ N _ _ _ c _)
    (p : IsoClass π B c) :
    (isoClassDerivedEquiv π B c S0).symm p =
      extOneNaiveDerivedEquiv A B N ((isoClassEquiv S0).symm p) :=
  sorry

/-- Lemma 92.16.1 (3) Given a solution B', the set of automorphisms of B' fitting
into (92.16.0.1) is canonically isomorphic to Ext⁽0⁾_B(L_{B/A}, N). The
automorphism type is FittingMap of the identity diagram compare S S. -/
@[stacks 08SP]
def autEquiv (S : @Solution A' A _ _ B _ _ π _ N _ _ _ c _) :
    Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N) ≃ FittingMap (compare S S) where
  toFun e :=
    -- Local instance justification (noncanonical choice): the B-action on N along compare S S is restriction along id.
    letI := RelativeDiagram.moduleRestrict (compare S S)
    FittingMap.perturb (compare S S) ((extZeroHomEquiv A B N).symm e) (idFitting S)
  invFun φ :=
    -- Local instance justification (noncanonical choice): the B-action on N along compare S S is restriction along id.
    letI := RelativeDiagram.moduleRestrict (compare S S)
    extZeroHomEquiv A B N (FittingMap.diff (compare S S) (idFitting S) φ)
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `autEquiv` sends an Ext⁰ class to the perturbation of `idFitting`. -/
theorem autEquiv_apply (S : @Solution A' A _ _ B _ _ π _ N _ _ _ c _)
    (e : Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N)) :
    autEquiv π B c S e =
      FittingMap.perturb (compare S S) ((extZeroHomEquiv A B N).symm e) (idFitting S) :=
  sorry

end SquareZeroExtension

end RingHom
