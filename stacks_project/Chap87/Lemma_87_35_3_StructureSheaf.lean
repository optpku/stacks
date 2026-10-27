/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.StructureSheaf
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap87.Definition_87_34_1_Site
public import stacks_project.Chap87.Lemma_87_34_4_Comparison
public import stacks_project.Chap87.Lemma_87_37_6_CountablyIndexed

/-!
# Compatibility for formal algebraic-space structure sheaves

The structure-sheaf recognition and stage-limit constructions use the active
reduction and its affine étale comparison through the source site interfaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsStructureSheaf :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [AlgebraicGeometry.FormalAlgebraicSpace.Reduction X],
    Sheaf (AlgebraicGeometry.FormalAlgebraicSpace.smallEtaleTopology X) RingCat.{u} → Prop)

#check (AlgebraicGeometry.FormalAlgebraicSpace.stageLimitRing :
  ∀ {S : Scheme.{u}} {Λ : Type u} [Preorder Λ], (Λ ⥤ Over S) → RingCat.{u})
