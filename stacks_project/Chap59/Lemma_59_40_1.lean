/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalHom
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 59.40.1: a scheme morphism induces a local morphism of small étale ringed sites. -/
@[stacks 04I5] #check (Scheme.Etale.Small.commRingedHom_isLocal :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
    (Scheme.Etale.Small.commRingedHom f).IsLocal)
