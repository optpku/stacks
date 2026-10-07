module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IntegralFinite

universe u

open CategoryTheory AlgebraicGeometry MorphismProperty

/- Lemma 67.45.1 (1): A representable morphism of algebraic spaces over `S` is
integral if and only if every affine scheme base change is affine and integral
over the base. -/
@[stacks 03ZO] #check
  (AlgebraicGeometry.AlgebraicSpace.integralHom_presheaf_iff_affineAndIntegralOnAffineSchemes :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      (hf : yoneda.relativelyRepresentable f),
      (over (@AlgebraicGeometry.IsIntegralHom : MorphismProperty Scheme.{u})).presheaf f ↔
        AlgebraicGeometry.AlgebraicSpace.affineAndIntegralOnAffineSchemes hf)

/- Lemma 67.45.1 (2): A representable morphism of algebraic spaces over `S` is
finite if and only if every affine scheme base change is affine and finite
over the base. -/
@[stacks 03ZO] #check
  (AlgebraicGeometry.AlgebraicSpace.finite_presheaf_iff_affineAndFiniteOnAffineSchemes :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      (hf : yoneda.relativelyRepresentable f),
      (over (@AlgebraicGeometry.IsFinite : MorphismProperty Scheme.{u})).presheaf f ↔
        AlgebraicGeometry.AlgebraicSpace.affineAndFiniteOnAffineSchemes hf)
