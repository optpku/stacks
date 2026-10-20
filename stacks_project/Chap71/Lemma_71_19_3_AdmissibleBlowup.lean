/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Admissible blowups of algebraic spaces

The shared admissibility API characterizes blowups with finitely presented
centers disjoint from a specified open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The open subspace determined by an open set of points. -/
noncomputable abbrev OpenSubspace.ofOpens {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : TopologicalSpace.Opens (Points X)) : OpenSubspace X :=
  OpenSubspace.fromOpens W

end AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsAdmissibleBlowup :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S},
    OpenSubspace X → (X' ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isAdmissibleBlowup_iff :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X),
    IsAdmissibleBlowup U f ↔
      ∃ Z : ClosedSubspace X,
        IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet)

