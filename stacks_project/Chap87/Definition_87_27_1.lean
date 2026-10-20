/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 87.27.1: a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is a closed immersion if it is representable by algebraic spaces and
a closed immersion in the sense of Bootstrap, Definition 80.4.1, i.e. the
Bootstrap transfer of closed immersions. The existing presheaf-level definition
applies in particular to formal algebraic spaces and tests every scheme Yoneda
pullback. -/
@[stacks 0ANP] #check (AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
