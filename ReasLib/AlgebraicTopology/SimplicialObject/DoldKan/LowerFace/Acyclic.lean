module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Decomposition
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateAcyclic
public import ReasLib.Algebra.Homology.HomologicalComplex.CokernelAcyclic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homological consequences of the source-signed lower-face decomposition

This leaf keeps the 019C consequences downstream of the concrete 019A decomposition.  The
normalized inclusion is a split inclusion whose complementary degenerate complex is acyclic.

@stack 019C
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

noncomputable section

universe v u

namespace AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The source-signed normalized inclusion into the alternating-face complex is a quasi-isomorphism.
-/
@[stacks 019C "source-signed normalized Moore inclusion quasi-isomorphism"]
theorem quasiIso (U : SimplicialObject A) :
    QuasiIso (normalizedMooreComplex.lowerFace.inclusion.app U) := sorry

/-- The cokernel of the source-signed normalized inclusion is acyclic. -/
@[stacks 019C "acyclic cokernel of the source-signed normalized Moore inclusion"]
theorem cokernel.acyclic (U : SimplicialObject A) :
    (cokernel (normalizedMooreComplex.lowerFace.inclusion.app U)).Acyclic := sorry

end AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion
