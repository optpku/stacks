/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 80.3.1: let `S` be a scheme contained in `Sch_fppf`. Let `F`, `G` be
presheaves on `(Sch/S)_fppf`. A morphism `a : F ⟶ G` is representable by algebraic
spaces if for every scheme `U` over `S` and any Yoneda section `ξ : yoneda.obj U ⟶ G`,
the fibre product `pullback ξ a` is an algebraic space. -/
@[stacks 02YQ] #check (@AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty ((CategoryTheory.Over S)ᵒᵖ ⥤ Type u))
