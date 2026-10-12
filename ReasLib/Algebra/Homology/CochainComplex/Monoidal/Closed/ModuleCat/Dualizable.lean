/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Iterated.Finite
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.Source

/-!
# Dualizability of bounded finite-projective module complexes

A bounded complex of finite-projective modules is dualizable in the closed monoidal category of
cochain complexes.  The dual object, comparison maps, evaluation, coevaluation, and exact pairing
remain owned by the generic `MonoidalClosed.Dual` API; this file supplies only the
finite-projective criterion needed to activate that API.

@stack 0658
@stack 0FNK
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [CommRing R]

/-- A bounded complex with finite-projective terms is a bounded finite-projective complex. -/
@[stacks 0658 "bounded termwise finite-projective complex"]
theorem of_bounded
    (M : CochainComplex (ModuleCat R) ℤ)
    (hM : CochainComplex.bounded (ModuleCat R) M)
    (hfp : ∀ n : ℤ, Module.FiniteProjective R (M.X n)) :
    M.IsBoundedFiniteProjective := sorry

/-- A bounded finite-projective module complex has invertible canonical
tensor-to-endomorphism comparison. -/
@[stacks 0FNK "dualizability of a bounded finite-projective complex", instance]
theorem isIso_tensorIhomUnitToEnd
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    IsIso (MonoidalClosed.tensorIhomUnitToEnd M) := sorry

/-- A bounded finite-projective module complex is right-dualizable. -/
@[stacks 0FNK "dualizability of a bounded finite-projective complex"]
theorem isRightDualizable
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    IsRightDualizable M := sorry

/-- A bounded finite-projective complex is canonically paired, in source order, with its
closed-monoidal dual. -/
@[stacks 0FNK "canonical dual pairing of a bounded finite-projective complex",
  implicit_reducible]
noncomputable def exactPairing
    (M : CochainComplex (ModuleCat R) ℤ) [M.IsBoundedFiniteProjective] :
    ExactPairing M (MonoidalClosed.dual M) :=
  MonoidalClosed.Dual.exactPairing M

/-- An explicit bounded finite-projective witness produces the canonical dual pairing without
installing that witness as a local instance. -/
@[stacks 0FNK "explicit witness for the canonical dual pairing", implicit_reducible]
noncomputable def exactPairingOf
    (M : CochainComplex (ModuleCat R) ℤ) (hM : M.IsBoundedFiniteProjective) :
    ExactPairing M (MonoidalClosed.dual M) :=
  @exactPairing R _ M hM

end CochainComplex.IsBoundedFiniteProjective
