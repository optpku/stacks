/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalScheme.Scheme

universe u

open CategoryTheory

/- 87.2.0.2: the comparison functor sends a scheme to the same underlying space and
structure-sheaf rings, with the pseudo-discrete topology on sections. -/
@[stacks 0AI0] #check (AlgebraicGeometry.Scheme.toFormalScheme.{u} :
  AlgebraicGeometry.Scheme.{u} ⥤ AlgebraicGeometry.FormalScheme.{u})
