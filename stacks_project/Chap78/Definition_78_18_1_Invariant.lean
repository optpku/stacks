/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Subobject.Invariant
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap78.Definition_78_4_1_PreRelation

/-!
# Invariant subspaces of a pre-relation

This module defines invariance of open subspaces, locally closed subspaces, and
monomorphisms under the source and target maps of a pre-relation in algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- An open subspace `W` of `U` is invariant under a pre-relation `P` when the restriction
of `P.t` to the inverse image of `W` along `P.s` factors through `W.ι`. -/
def IsOpenInvariant (P : PreRelation U) (W : OpenSubspace U.left) : Prop :=
  CategoryTheory.Morphism.IsForwardInvariant P.s.left P.t.left W.ι

/-- A locally closed subspace `Z` of `U` is invariant under a pre-relation `P` when the
inverse images of `Z` along `P.t` and `P.s` agree as objects over the relation space. -/
def IsLocallyClosedInvariant (P : PreRelation U) (Z : LocallyClosedSubspace U.left) : Prop :=
  CategoryTheory.Morphism.IsPullbackInvariant P.s.left P.t.left Z.ι

/-- A subobject of `U` is invariant under a pre-relation `P` when its pullbacks along
`P.t` and `P.s` agree. -/
def IsInvariant (P : PreRelation U) (Q : Subobject U.left) : Prop :=
  CategoryTheory.Subobject.IsInvariant P.s.left P.t.left Q

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
