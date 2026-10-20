module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Flat.EtaleProjectiveCover
import StacksCheckRecall

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

/- Lemma 77.5.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `F` be a quasi-coherent sheaf on `X`. Let `y : Points Y`.
Assume that `f` is of finite presentation, `F` is of finite presentation, and `F`
is flat over `Y` at every point of the fibre `fiberOver f y`. Then there
exists a commutative étale square covering that fibre by affine algebraic spaces
`X'` and `Y'`, together with a point of `Y'` mapping to `y`, such that
`Γ(X', g^* F)` is a projective `Γ(Y', ⊤)`-module. -/
@[stacks 0CVZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.existsAffineEtaleCoverWithProjectiveSections :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (y : Points Y) (h_flat : ∀ x ∈ fiberOver f y, flatOverAt F f x),
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
                (Scheme.Hom.sectionsMod sq.map.left ⊤ ⊤ le_top F'))

end AlgebraicGeometry.AlgebraicSpace.Modules
