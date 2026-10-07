module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap76.Lemma_76_36_2_PointsOver

/-!
# Affine étale covers with projective sections along a fibre

If a morphism of algebraic spaces is of finite presentation and a finitely presented
module is flat at every point of a fibre, then after affine étale refinements covering
that fibre the pulled-back global sections are projective over the refined base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 77.5.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `F` be a quasi-coherent sheaf on `X`. Let `y : Points Y`.
Assume that `f` is of finite presentation, `F` is of finite presentation, and `F`
is flat over `Y` at every point of the fibre `Hom.pointsOver f y`. Then there
exists a commutative étale square covering that fibre by affine algebraic spaces
`X'` and `Y'`, together with a point of `Y'` mapping to `y`, such that
`Γ(X', g^* F)` is a projective `Γ(Y', ⊤)`-module. -/
@[stacks 0CVZ]
theorem existsAffineEtaleCoverWithProjectiveSections
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (y : Points Y) (h_flat : ∀ x ∈ Hom.pointsOver f y, flatOverAt F f x) :
    ∃ sq : EtaleSquare f,
      let U := sq.left
      let V := sq.right
      let X' := U.left.left
      let Y' := V.left.left
      let F' := (restrictToScheme U).obj F
      ∃ y' : Y',
        IsAffine X' ∧ IsAffine Y' ∧
          Points.map V.hom (ofOver.pointsEquiv V.left y') = y ∧
            Hom.pointsOver f y ⊆ Set.range (Points.map U.hom) ∧
              Module.Projective Γ(Y', ⊤)
                (Scheme.Hom.sectionsMod sq.map.left ⊤ ⊤ le_top F') :=
  sorry

/-- Existence of an affine étale square covering the fibre `Hom.pointsOver f y` on
which `g^* F` has projective global sections unpacks as étale morphisms from affine
schemes over `S`, a commuting comparison, a point of `Y'` mapping to `y`, and the
fibre contained in the image of `|X'|`. -/
theorem existsAffineEtaleCoverWithProjectiveSections_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (y : Points Y) (h_flat : ∀ x ∈ Hom.pointsOver f y, flatOverAt F f x) :
    ∃ (U V : Over S) (g : ofOver U ⟶ X) (h : ofOver V ⟶ Y) (φ : U ⟶ V) (y' : V.left)
        (hg : Etale g) (hh : Etale h),
      IsAffine U.left ∧ IsAffine V.left ∧ g ≫ f = ofOverMap φ ≫ h ∧
        Points.map h (ofOver.pointsEquiv V y') = y ∧
          Hom.pointsOver f y ⊆ Set.range (Points.map g) ∧
            Module.Projective Γ(V.left, ⊤)
              (Scheme.Hom.sectionsMod φ.left ⊤ ⊤ le_top
                ((restrictToScheme (smallEtaleSite.mk g)).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
