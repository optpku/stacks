module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme

/-!
# Affine étale refinements with projective sections

A finitely presented module flat at a point over a locally finitely presented morphism of
algebraic spaces has projective global sections after suitable affine étale refinements.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finitely presented module flat at a point over a locally finitely presented morphism
of algebraic spaces admits affine étale scheme charts through that point on which its
global sections are projective over the target chart's ring of global sections. -/
@[stacks 0CVY]
theorem existsAffineEtaleRefinementWithProjectiveSections
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (x : Points X) (h_flat : flatOverAt F f x) :
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
              (Scheme.Hom.sectionsMod sq.map.left ⊤ ⊤ le_top F') :=
  sorry

/-- Existence of an affine étale scheme square over `f` on which `g^* F` has projective
global sections unpacks as étale morphisms from affine schemes over `S`, a commuting
comparison, and a source point mapping to `x` whose image on `Y'` maps to `Points.map f x`. -/
theorem existsAffineEtaleRefinementWithProjectiveSections_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (x : Points X) :
    (∃ sq : EtaleSquare f,
      let U := sq.left
      let V := sq.right
      let X' := U.left.left
      let Y' := V.left.left
      let F' := (restrictToEtaleScheme U).obj F
      ∃ x' : X',
        Points.map U.hom (ofOver.pointsEquiv U.left x') = x ∧
          IsAffine X' ∧ IsAffine Y' ∧
            Module.Projective Γ(Y', ⊤)
              (Scheme.Hom.sectionsMod sq.map.left ⊤ ⊤ le_top F')) ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (x' : U.left)
        (ha : Etale a) (hb : Etale b),
        IsAffine U.left ∧ IsAffine V.left ∧ a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U x') = x ∧
            Points.map b (ofOver.pointsEquiv V (h.left x')) = Points.map f x ∧
              Module.Projective Γ(V.left, ⊤)
                (Scheme.Hom.sectionsMod h.left ⊤ ⊤ le_top
                  ((restrictToEtaleScheme
                    (MorphismProperty.CostructuredArrow.mk ⊤ a ha)).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
