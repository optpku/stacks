module

public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra
public import stacks_project.Chap67.Lemma_67_48_1_IntegralClosure

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- Lemma 67.48.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `A` be a
quasi-coherent sheaf of `𝒪_X`-algebras. There exists a quasi-coherent sheaf of `𝒪_X`-algebras
`A' ⊂ A` such that for any affine object `U` of `X_étale` the ring `A'(U) ⊂ A(U)` is the
integral closure of `𝒪_X(U)` in `A(U)`. The constructed algebra is `integralClosure A`, and
the identification on affine étale objects is with mathlib `integralClosure`. -/
@[stacks 0820]
theorem affine_sectionRing_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (U : affineEtaleSite X) :
    sectionRing (integralClosure A) U.obj =
      CommRingCat.of (_root_.integralClosure Γ(U.obj.left.left, ⊤) (sectionRing A U.obj)) :=
  sorry

/-- The inclusion `integralClosure A ⟶ A` is a monomorphism of underlying sheaves of algebras. -/
theorem inclusion_mono {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    Mono ((forget X).map (inclusion A)).right :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
