module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.EtaleProjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 38.12.6: a scheme morphism locally of finite presentation and flat at a point
admits affine elementary étale refinements on which the refined source's global sections
are projective over the refined target's global sections. -/
@[stacks 05IE] #check
  (AlgebraicGeometry.Scheme.Hom.existsAffineEtaleRefinementWithProjectiveSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (x : X) (h_flat : f.flatAt x),
    ∃ square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x,
      let X' := square.source.obj.toEtale.left
      let S' := square.base.obj.toEtale.left
      IsAffine X' ∧ IsAffine S' ∧
        Module.Projective Γ(S', ⊤)
          (Scheme.Hom.sectionsMod square.map ⊤ ⊤ le_top (𝟙_ X'.Modules)))

end AlgebraicGeometry.Scheme.Hom
