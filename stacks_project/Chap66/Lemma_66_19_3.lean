/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.Cofiltered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.19.3 (1): for a scheme `S`, an algebraic space `X` over `S`, and a geometric point
`xbar` of `X`, the category of étale neighborhoods of `xbar` is cofiltered. -/
@[stacks 04JW] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.instIsCofiltered :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X),
      IsCofiltered (GeometricPoint.EtaleNeighborhood xbar))

section

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)

/- Lemma 66.19.3 (2): any two étale neighborhoods of a geometric point of an algebraic space
admit a third mapping to both. -/
@[stacks 04JW] #check (CategoryTheory.IsCofilteredOrEmpty.cone_objs :
  ∀ (U₁ U₂ : GeometricPoint.EtaleNeighborhood xbar),
    ∃ (U : GeometricPoint.EtaleNeighborhood xbar) (_ : U ⟶ U₁) (_ : U ⟶ U₂), True)

/- Lemma 66.19.3 (3): any two parallel morphisms of étale neighborhoods of a geometric point of
an algebraic space can be equalized by a further neighborhood. -/
@[stacks 04JW] #check (CategoryTheory.IsCofilteredOrEmpty.cone_maps :
  ∀ ⦃U U' : GeometricPoint.EtaleNeighborhood xbar⦄ (h1 h2 : U ⟶ U'),
    ∃ (U'' : GeometricPoint.EtaleNeighborhood xbar) (h : U'' ⟶ U), h ≫ h1 = h ≫ h2)

end

/- Lemma 66.19.3 (4): given any étale neighborhood of a geometric point of an algebraic space,
there is a morphism from an étale neighborhood whose underlying object is a scheme. -/
@[stacks 04JW] #check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.exists_isScheme :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}
    (U : GeometricPoint.EtaleNeighborhood xbar),
    ∃ (U' : GeometricPoint.EtaleNeighborhood xbar) (_ : U' ⟶ U), IsScheme U'.space)
