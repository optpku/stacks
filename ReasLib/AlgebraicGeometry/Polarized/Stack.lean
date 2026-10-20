/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

/-!
# Stacks in groupoids of polarized proper schemes

Polarized proper schemes form a stack in groupoids over proper flat finitely
presented algebraic-space families with the inherited fppf topology and over the
fppf site of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The forgetful functor from polarized proper schemes to proper flat finitely
presented algebraic-space families is a stack in groupoids for the inherited
fppf topology. -/
@[stacks 0D40]
instance instIsStackInGroupoids_toFpFlatProper :
    IsStack.InGroupoids
      ((pFpFlatProperGroupoids (⊤_ Scheme.{u})).inheritedTopology
        (Scheme.fppfTopology.over (⊤_ Scheme.{u})))
      toFpFlatProper :=
  sorry

/-- The base-scheme functor of polarized proper schemes is a stack in groupoids
for the fppf topology. -/
@[stacks 0D40]
instance instIsStackInGroupoids : IsStack.InGroupoids Scheme.fppfTopology p :=
  sorry

end AlgebraicGeometry.Polarized
