module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjective
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finitely presented scheme morphism that is flat at a point admits affine
elementary étale refinements whose source global sections are projective over those of
the refined base. -/
theorem existsAffineEtaleRefinementWithProjectiveSections {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) (h_flat : f.flatAt x) :
    ∃ square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x,
      let X' := square.source.obj.toEtale.left
      let S' := square.base.obj.toEtale.left
      IsAffine X' ∧ IsAffine S' ∧
        Module.Projective Γ(S', ⊤)
          (Scheme.Hom.sectionsMod square.map ⊤ ⊤ le_top (𝟙_ X'.Modules)) := sorry

end AlgebraicGeometry.Scheme.Hom
