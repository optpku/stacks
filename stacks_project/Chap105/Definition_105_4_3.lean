/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnSchemes
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 105.4.3: a morphism `S ⟶ ℳ_{1,1}` is smooth if for every
morphism `S' ⟶ ℳ_{1,1}` the projection `S ×_{ℳ_{1,1}} S' ⟶ S'` is a
smooth morphism of schemes. The same pattern applies to other morphism
properties and other moduli stacks. -/
@[stacks 072P] #check (AlgebraicGeometry.Groupoids.Hom.SmoothOnSchemes :
    ∀ {B : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver B}
      {S : CategoryTheory.Over B}, (AlgebraicGeometry.GroupoidsOver.slice S ⟶ X) → Prop)
