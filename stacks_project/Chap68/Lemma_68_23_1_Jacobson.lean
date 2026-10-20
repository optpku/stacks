/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson
public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_7_1
public import stacks_project.Chap66.Lemma_66_7_1_EtaleLocal
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal

/-!
# Jacobson algebraic spaces

An algebraic space is Jacobson when it admits a representable étale locally-surjective
atlas from a Jacobson scheme, equivalently when every étale morphism from a scheme has
Jacobson source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsJacobson.iff_forallEtale :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.IsJacobson X ↔
      AlgebraicGeometry.AlgebraicSpace.forallEtale (fun U : Scheme.{u} ↦ JacobsonSpace U) X)
