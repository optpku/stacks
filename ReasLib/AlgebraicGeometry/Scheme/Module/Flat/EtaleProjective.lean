/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Square
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.Algebra.Module.Projective

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module flat at a point over a locally finitely presented scheme
morphism has affine elementary étale refinements on which its pulled-back global sections
are projective over the refined base. -/
theorem existsAffineEtaleRefinementWithProjectiveSections {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (h_flat : flatOverAt F f x) :
    ∃ square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x,
      let X' := square.source.obj.toEtale.left
      let S' := square.base.obj.toEtale.left
      let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
      IsAffine X' ∧ IsAffine S' ∧
        Module.Projective Γ(S', ⊤)
          (Scheme.Hom.sectionsMod square.map ⊤ ⊤ le_top F') := sorry

end AlgebraicGeometry.Scheme.Modules
