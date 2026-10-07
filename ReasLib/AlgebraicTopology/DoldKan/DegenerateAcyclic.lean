module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateContractible
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateDecomposition.Canonical
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateDecomposition.Degreewise
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclicity consequences of the Dold--Kan degenerate decomposition

This leaf records the abelian-category and homological consequences of the
normalized-plus-degenerate splitting, independently of any textbook chapter. The constructive
contraction is available separately from `DegenerateContractible`.

@stack 019C
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open scoped DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace QInfty

/-- The canonical chain-level image of `QInfty` is acyclic in an abelian category. -/
@[stacks 019C "acyclicity of the canonical QInfty image"]
theorem acyclic (U : SimplicialObject A) :
    (QInfty.image U).Acyclic := sorry

end QInfty

namespace degenerateComplex

/-- The degenerate summand in the Dold--Kan decomposition is acyclic. -/
@[stacks 019C "acyclicity of the degenerate complex"]
theorem acyclic (U : SimplicialObject A) :
    D[U].Acyclic := sorry

end degenerateComplex

end AlgebraicTopology.DoldKan

namespace AlgebraicTopology.normalizedMooreComplex.inclusion

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical normalized-Moore inclusion into the alternating-face complex is a
quasi-isomorphism. -/
@[stacks 019C "normalized Moore inclusion quasi-isomorphism"]
theorem quasiIso (U : SimplicialObject A) :
    QuasiIso (inclusionOfMooreComplexMap U) := sorry

namespace cokernel

/-- The cokernel of the normalized-Moore inclusion into the alternating-face complex is
acyclic. -/
@[stacks 019C "acyclic cokernel of the normalized Moore inclusion"]
theorem acyclic (U : SimplicialObject A) :
    (cokernel (inclusionOfMooreComplexMap U)).Acyclic := sorry

end cokernel

end AlgebraicTopology.normalizedMooreComplex.inclusion

namespace AlgebraicTopology.DoldKan.normalizedMoore.inclusion

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Deprecated compatibility name for the canonical normalized-Moore inclusion
quasi-isomorphism. -/
@[deprecated AlgebraicTopology.normalizedMooreComplex.inclusion.quasiIso
  (since := "2026-08-06")]
alias quasiIso := AlgebraicTopology.normalizedMooreComplex.inclusion.quasiIso

namespace cokernel

/-- Deprecated compatibility name for acyclicity of the canonical normalized-Moore
inclusion's cokernel. -/
@[deprecated AlgebraicTopology.normalizedMooreComplex.inclusion.cokernel.acyclic
  (since := "2026-08-06")]
alias acyclic := AlgebraicTopology.normalizedMooreComplex.inclusion.cokernel.acyclic

end cokernel

end AlgebraicTopology.DoldKan.normalizedMoore.inclusion
