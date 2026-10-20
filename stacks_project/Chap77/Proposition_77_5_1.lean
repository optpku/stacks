/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.EtaleProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Proposition 77.5.1: A finitely presented quasi-coherent module flat at a point over a
locally finitely presented morphism of algebraic spaces admits affine étale pointed scheme
refinements with global sections projective over the target chart's ring. -/
@[stacks 0CVY] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.existsAffineEtaleRefinementWithProjectiveSections :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (x : Points X) (h_flat : flatOverAt F f x),
    ∃ sq : EtaleSquare f,
      let U := sq.left
      let V := sq.right
      let X' := U.left.left
      let Y' := V.left.left
      let F' := (restrictToEtaleScheme U).obj F
      ∃ x' : X',
        Points.map U.hom (ofOver.pointsEquiv U.left x') = x ∧
          IsAffine X' ∧ IsAffine Y' ∧
            Module.Projective Γ(Y', ⊤)
              (Scheme.Hom.sectionsMod sq.map.left ⊤ ⊤ le_top F'))
