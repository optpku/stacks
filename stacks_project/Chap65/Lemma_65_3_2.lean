/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.MorphismProperty.Representable.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

variable {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
variable (a : F ⟶ G) (b : G ⟶ H)
variable (ha : yoneda.relativelyRepresentable a) (hb : yoneda.relativelyRepresentable b)

/- Lemma 65.3.2: let `S` be a scheme and let `F`, `G`, `H` be functors
`(Over S)ᵒᵖ ⥤ Type u`. If `a : F ⟶ G` and `b : G ⟶ H` are representable transformations
of functors, then the composite `a ≫ b : F ⟶ H` is a representable transformation of functors. -/
@[stacks 02WA]
#check (CategoryTheory.Functor.relativelyRepresentable.comp_mem a b ha hb :
  yoneda.relativelyRepresentable (a ≫ b))
