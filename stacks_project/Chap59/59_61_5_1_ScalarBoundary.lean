/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_61_5_Cohomology
public import ReasLib.Algebra.GroupCohomology.ProjectiveLinearBoundary
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

@[expose] public section

universe u v

open scoped MatrixGroups

namespace Matrix.ProjGenLinGroup

variable {R : Type u} [CommRing R]

#check (kernelScalarUnit : ∀ (d : ℕ), 0 < d →
  (mk : GL (Fin d) R →* PGL(d, R)).ker → Rˣ)

#check (scalarToKer : ∀ d : ℕ,
  Rˣ → (mk : GL (Fin d) R →* PGL(d, R)).ker)

#check (scalarEquivKer : ∀ (d : ℕ), 0 < d →
  Rˣ ≃* (mk : GL (Fin d) R →* PGL(d, R)).ker)

#check (scalarEquivKer_apply : ∀ (d : ℕ) (hd : 0 < d) (unit : Rˣ),
  (scalarEquivKer d hd unit).1 = GeneralLinearGroup.scalar (Fin d) unit)

#check (scalarEquivKer_symm_spec : ∀ (d : ℕ) (hd : 0 < d)
  (A : (mk : GL (Fin d) R →* PGL(d, R)).ker),
  scalarToKer d ((scalarEquivKer d hd).symm A) = A)

end Matrix.ProjGenLinGroup

namespace GroupCohomology

variable {G : Type u} {R : Type v} [Group G] [Field R] [MulSemiringAction G R]

#check (galoisGLAction : ∀ d : ℕ, MulDistribMulAction G (GL (Fin d) R))

#check (galoisUnitsAction : MulDistribMulAction G Rˣ)

end GroupCohomology

end
