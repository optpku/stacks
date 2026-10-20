/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth

/-!
# Smooth groupoids in algebraic spaces

A groupoid in algebraic spaces is smooth when its source and target maps are
smooth morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, GroupoidAlgebraicSpace B → Prop)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth.source :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B},
    Smooth G → AlgebraicSpace.Smooth G.s.left)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth.target :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B},
    Smooth G → AlgebraicSpace.Smooth G.t.left)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth.discrete :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B),
    Smooth (GroupoidAlgebraicSpace.discrete U))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth.iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    Smooth G ↔ AlgebraicSpace.Smooth G.s.left ∧ AlgebraicSpace.Smooth G.t.left)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth.source_iff_target :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
    AlgebraicSpace.Smooth G.s.left ↔ AlgebraicSpace.Smooth G.t.left)

end AlgebraicGeometry.GroupoidAlgebraicSpace
