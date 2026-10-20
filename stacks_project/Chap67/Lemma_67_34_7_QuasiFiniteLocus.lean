/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_23_3_Pullback
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_34_4_FiberDimensionLocus

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus

/-!
# Quasi-finite locus of a locally finite-type morphism of algebraic spaces

The canonical open subspace consists of the points at which the morphism is
quasi-finite, equivalently the relative-dimension-zero locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f], OpenSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.mem_quasiFiniteLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : Points X),
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ x ∈ fiberDimensionLELocus f 0)

#check (AlgebraicGeometry.AlgebraicSpace.mem_quasiFiniteLocus_iff_relativeDimensionLEAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : Points X),
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ RelativeDimensionLEAt f 0 x)

#check (AlgebraicGeometry.AlgebraicSpace.mem_quasiFiniteLocus_iff_quasiFiniteAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : Points X),
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ QuasiFiniteAt f x)

end AlgebraicGeometry.AlgebraicSpace
