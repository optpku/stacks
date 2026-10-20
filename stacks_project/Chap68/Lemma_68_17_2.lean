/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications
import StacksCheckRecall

/-!
# Implications among relative conditions

A morphism of algebraic spaces that is representable or quasi-separated is very
reasonable, and very reasonableness implies reasonableness, decency, and
property (β).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.17.2 (1): representable implies very reasonable. -/
@[stacks 03M5] #check
  (AlgebraicGeometry.AlgebraicSpace.VeryReasonable.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f), VeryReasonable f)

/- Lemma 68.17.2 (2): quasi-separated implies very reasonable. -/
@[stacks 03M5] #check
  (AlgebraicGeometry.AlgebraicSpace.VeryReasonable.of_quasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiSeparated f], VeryReasonable f)

/- Lemma 68.17.2 (3): very reasonable implies reasonable. -/
@[stacks 03M5] #check
  (AlgebraicGeometry.AlgebraicSpace.Reasonable.of_veryReasonable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [VeryReasonable f], Reasonable f)

/- Lemma 68.17.2 (4): reasonable implies decent. -/
@[stacks 03M5] #check
  (AlgebraicGeometry.AlgebraicSpace.Decent.of_reasonable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Reasonable f], Decent f)

/- Lemma 68.17.2 (5): decent implies property (β). -/
@[stacks 03M5] #check
  (AlgebraicGeometry.AlgebraicSpace.PropertyBeta.of_decent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Decent f], PropertyBeta f)

end AlgebraicGeometry.AlgebraicSpace
