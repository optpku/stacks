/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hyperplane
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

/-!
# Bertini theorem for projective hyperplane sections

A smooth irreducible scheme of dimension at least two over an algebraically closed field has a
smooth irreducible hyperplane section in any chosen projective presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectivePresentation

/-- A smooth irreducible scheme of dimension at least two over an algebraically closed field has a
smooth irreducible hyperplane section in any chosen projective presentation. -/
theorem exists_smooth_irreducible_hyperplaneSection
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] [IrreducibleSpace X.left]
    (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n) (i : X.left ⟶ P.scheme)
    (h_i : ProjectivePresentation X.hom P.hom i)
    (h_dim : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X.left) :
    ∃ (H : Scheme.{u}) (j : H ⟶ P.scheme),
      ProjectiveSpaceHyperplane P j ∧
        (Smooth (Limits.pullback.fst i j ≫ X.hom) ∧
          IrreducibleSpace (Limits.pullback i j : Scheme.{u})) := sorry

end AlgebraicGeometry.ProjectivePresentation
