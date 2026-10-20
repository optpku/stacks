module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite Projective Cochain Complexes

This file owns finiteness and projectivity predicates for cochain complexes
of modules.  The derived-category consequences belong in separate leaves.
@stack 0658
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

namespace CochainComplex

variable {R : Type u} [Ring R]

/-- A cochain complex of `R`-modules is bounded finite projective if it is bounded on both sides
and each term is a finite projective `R`-module. -/
class IsBoundedFiniteProjective (L : CochainComplex (ModuleCat R) ℤ) : Prop where
  /-- The complex is bounded on both sides. -/
  bounded : ∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b
  /-- Each term is a finite `R`-module. -/
  finite (n : ℤ) : Module.Finite R (L.X n)
  /-- Each term is a projective `R`-module. -/
  projective (n : ℤ) : Module.Projective R (L.X n)

/-- A cochain complex is finite projective in `[a, b]` when it is supported in that interval and
all of its terms are finite projective modules. -/
@[stacks 0658 "finite-projective complex in a fixed interval"]
def IsFiniteProjectiveIn (L : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) : Prop :=
  L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
    ∀ n : ℤ, Module.Finite R (L.X n) ∧ Module.Projective R (L.X n)

namespace IsFiniteProjectiveIn

/-- A complex finite projective in `[a, b]` vanishes below `a`. -/
theorem isStrictlyGE {L : CochainComplex (ModuleCat R) ℤ} {a b : ℤ}
    (hL : L.IsFiniteProjectiveIn a b) :
    L.IsStrictlyGE a := sorry

/-- A complex finite projective in `[a, b]` vanishes above `b`. -/
theorem isStrictlyLE {L : CochainComplex (ModuleCat R) ℤ} {a b : ℤ}
    (hL : L.IsFiniteProjectiveIn a b) :
    L.IsStrictlyLE b := sorry

/-- Every term of a complex finite projective in a fixed interval is finite. -/
theorem finite {L : CochainComplex (ModuleCat R) ℤ} {a b : ℤ}
    (hL : L.IsFiniteProjectiveIn a b) (n : ℤ) :
    Module.Finite R (L.X n) := sorry

/-- Every term of a complex finite projective in a fixed interval is projective. -/
theorem projective {L : CochainComplex (ModuleCat R) ℤ} {a b : ℤ}
    (hL : L.IsFiniteProjectiveIn a b) (n : ℤ) :
    Module.Projective R (L.X n) := sorry

/-- A complex finite projective in a fixed interval is bounded finite projective. -/
theorem isBoundedFiniteProjective {L : CochainComplex (ModuleCat R) ℤ} {a b : ℤ}
    (hL : L.IsFiniteProjectiveIn a b) :
    L.IsBoundedFiniteProjective := sorry

end IsFiniteProjectiveIn

/-- A bounded finite-projective complex is exactly a bounded complex with termwise finite
projective terms. -/
theorem isBoundedFiniteProjective_iff (L : CochainComplex (ModuleCat R) ℤ) :
    IsBoundedFiniteProjective L ↔
      (∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b) ∧
        (∀ n : ℤ, Module.Finite R (L.X n)) ∧
          ∀ n : ℤ, Module.Projective R (L.X n) := sorry

/-- Terms of a bounded finite-projective complex are finite modules. -/
instance (L : CochainComplex (ModuleCat R) ℤ) [h : IsBoundedFiniteProjective L] (n : ℤ) :
    Module.Finite R (L.X n) :=
  h.finite n

/-- Terms of a bounded finite-projective complex are projective modules. -/
instance (L : CochainComplex (ModuleCat R) ℤ) [h : IsBoundedFiniteProjective L] (n : ℤ) :
    Module.Projective R (L.X n) :=
  h.projective n

/-- A graded `R`-module, presented as a cochain complex, is finite when the direct sum of all
homogeneous pieces is a finite `R`-module. -/
def IsFiniteGraded (P : CochainComplex (ModuleCat R) ℤ) : Prop :=
  Module.Finite R (⨁ n : ℤ, P.X n)

/-- The finite graded condition is finite generation of the direct sum of the homogeneous terms.
-/
theorem isFiniteGraded_iff (P : CochainComplex (ModuleCat R) ℤ) :
    P.IsFiniteGraded ↔ Module.Finite R (⨁ n : ℤ, P.X n) :=
  Iff.rfl

/-- A graded `R`-module, presented as a cochain complex, is finite graded projective when its
graded direct sum is finite and every homogeneous piece is projective. -/
def IsFiniteGradedProjective (P : CochainComplex (ModuleCat R) ℤ) : Prop :=
  P.IsFiniteGraded ∧ ∀ n : ℤ, Module.Projective R (P.X n)

/-- The finite graded projective condition separates into graded finiteness and termwise
projectivity. -/
theorem isFiniteGradedProjective_iff (P : CochainComplex (ModuleCat R) ℤ) :
    P.IsFiniteGradedProjective ↔
      P.IsFiniteGraded ∧ ∀ n : ℤ, Module.Projective R (P.X n) :=
  Iff.rfl

namespace IsFiniteGradedProjective

/-- A finite graded projective complex is finite as a graded module. -/
theorem isFiniteGraded {P : CochainComplex (ModuleCat R) ℤ} (hP : P.IsFiniteGradedProjective) :
    P.IsFiniteGraded :=
  hP.1

/-- Each homogeneous component of a finite graded projective complex is projective. -/
theorem projective {P : CochainComplex (ModuleCat R) ℤ} (hP : P.IsFiniteGradedProjective) (n : ℤ) :
    Module.Projective R (P.X n) :=
  hP.2 n

/-- A finite graded projective complex has finite support and is therefore bounded finite
projective. -/
theorem isBoundedFiniteProjective {P : CochainComplex (ModuleCat R) ℤ}
    (hP : P.IsFiniteGradedProjective) :
    P.IsBoundedFiniteProjective := sorry

end IsFiniteGradedProjective

end CochainComplex
