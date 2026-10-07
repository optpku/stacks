module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

/-!
# Affine étale refinements with projective sections

If a morphism of algebraic spaces is locally of finite presentation and a finitely presented
module is flat at a point over the target, then after affine étale refinements of the pointed
source and target the pulled-back global sections are projective over the refined base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Proposition 77.5.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `F` be a quasi-coherent sheaf on `X`. Let `x : Points X` with image
`Points.map f x`. Assume that `f` is locally of finite presentation, `F` is of finite
presentation, and `F` is flat at `x` over `Y`. Then there exists a commutative square of
pointed schemes with étale horizontals from affine schemes `X'` and `Y'` such that
`Γ(X', g^* F)` is a projective `Γ(Y', ⊤)`-module. -/
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
      let F' := (restrictToScheme U).obj F
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
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (x : Points X) (h_flat : flatOverAt F f x) :
    (∃ sq : EtaleSquare f,
      let U := sq.left
      let V := sq.right
      let X' := U.left.left
      let Y' := V.left.left
      let F' := (restrictToScheme U).obj F
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
                  ((restrictToScheme (smallEtaleSite.mk a)).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
