/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap78.Definition_78_4_1_PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoretic

/-!
# Set-theoretic (pre-)equivalence relations

A pre-relation on an algebraic space is a set-theoretic pre-equivalence relation when the
relation on algebraically closed field-valued points, allowing a field-extension witness, is
an equivalence relation. It is a set-theoretic equivalence relation when this holds and the
defining map is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsSetTheoreticPreEquivalence :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}, PreRelation U → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsSetTheoreticEquivalence :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}, PreRelation U → Prop)

end AlgebraicGeometry.AlgebraicSpace
