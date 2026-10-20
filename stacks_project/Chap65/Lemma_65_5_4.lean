/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

/- Lemma 65.5.4 -/
@[stacks 02WK] #check
  (AlgebraicGeometry.Scheme.representableMorphismProperty.comp_mem :
    ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
      [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
      [P.IsStableUnderComposition] {F G H : (Over S)ᵒᵖ ⥤ Type u}
      (a : F ⟶ G) (b : G ⟶ H)
      (ha : AlgebraicGeometry.Scheme.representableMorphismProperty S P a)
      (hb : AlgebraicGeometry.Scheme.representableMorphismProperty S P b),
      AlgebraicGeometry.Scheme.representableMorphismProperty S P (a ≫ b))
