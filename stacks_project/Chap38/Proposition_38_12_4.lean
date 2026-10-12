/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Proposition 38.12.4: a finitely presented module that is flat at a point over a
locally finitely presented scheme morphism becomes projective on global sections after
affine elementary étale refinements of the pointed source and target. -/
@[stacks 05ID] #check
  (AlgebraicGeometry.Scheme.Modules.existsAffineEtaleRefinementWithProjectiveSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsFinitePresentation] (x : X) (h_flat : flatOverAt F f x),
    ∃ square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x,
      let X' := square.source.obj.toEtale.left
      let S' := square.base.obj.toEtale.left
      let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
      IsAffine X' ∧ IsAffine S' ∧
        Module.Projective Γ(S', ⊤)
          (Scheme.Hom.sectionsMod square.map ⊤ ⊤ le_top F'))

end AlgebraicGeometry.Scheme.Modules
