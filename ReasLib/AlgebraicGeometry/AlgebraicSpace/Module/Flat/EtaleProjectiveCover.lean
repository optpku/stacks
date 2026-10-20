module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber

/-!
# Affine étale covers with projective sections along a fibre

A finitely presented module flat along a fibre of a finitely presented morphism of
algebraic spaces admits affine étale charts covering that fibre, with projective
restricted global sections over the target chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finitely presented module flat along a fibre of a finitely presented morphism of
algebraic spaces admits a commutative square of affine étale scheme charts whose source
image contains the entire fibre and whose target has a point above the specified point,
such that the restricted global sections are projective over the target's section ring. -/
theorem existsAffineEtaleCoverWithProjectiveSections
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (y : Points Y) (h_flat : ∀ x ∈ fiberOver f y, flatOverAt F f x) :
    ∃ sq : EtaleSquare f,
      let U := sq.left
      let V := sq.right
      let X' := U.left.left
      let Y' := V.left.left
      let F' := (restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj F
      ∃ y' : Y',
        IsAffine X' ∧ IsAffine Y' ∧
          Points.map V.hom (ofOver.pointsEquiv V.left y') = y ∧
            fiberOver f y ⊆ Set.range (Points.map U.hom) ∧
              Module.Projective Γ(Y', ⊤)
                (Scheme.Hom.sectionsMod sq.map.left ⊤ ⊤ le_top F') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
