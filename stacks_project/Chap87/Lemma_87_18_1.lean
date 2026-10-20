/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_12_1_Reduction
public import stacks_project.Chap87.Lemma_87_18_1_Colimit
public import stacks_project.Chap87.Lemma_87_18_1_QuasiSeparated

/-!
# Lemma 87.18.1

A quasi-compact quasi-separated formal algebraic space is isomorphic, as an
fppf sheaf, to a directed colimit of algebraic spaces along thickening
transitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.18.1: Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated formal algebraic space over `S`. Then `X` is isomorphic, as an
fppf sheaf, to a directed colimit of algebraic spaces whose transition maps
are thickenings. -/
@[stacks 0AJE]
theorem exists_directedAlgebraicSpaceThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsQuasiSeparatedFormalAlgebraicSpace X]
    [ChosenBigFppfSite.IsQuasiCompact (reduction X)] :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D X :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
