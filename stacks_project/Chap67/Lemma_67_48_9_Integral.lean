/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Integral quasi-coherent algebras on algebraic spaces

A quasi-coherent `𝒪_X`-algebra is integral when its section algebras on affine
étale objects are integral over the corresponding structure-sheaf sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- A quasi-coherent `𝒪_X`-algebra is integral if, for every affine object of `X_étale`,
the algebra of sections is integral over the corresponding structure-sheaf sections. -/
class IsIntegral {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) : Prop where
  /-- Section algebras on affine étale objects are integral. -/
  isIntegral_affineEtale :
    ∀ U : affineEtaleSite X,
      Algebra.IsIntegral Γ(U.obj.left.left, ⊤) (sectionRing A U.obj)

/-- Integrality of a quasi-coherent `𝒪_X`-algebra is equivalent to integrality of its
section algebras on every affine étale object. -/
theorem isIntegral_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    IsIntegral A ↔
      ∀ U : affineEtaleSite X,
        Algebra.IsIntegral Γ(U.obj.left.left, ⊤) (sectionRing A U.obj) :=
  sorry

/-- Integrality of a quasi-coherent `𝒪_X`-algebra is equivalent to integrality of the
structure-map components on every affine étale object. -/
theorem isIntegral_iff_ringHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    IsIntegral A ↔
      ∀ U : affineEtaleSite X, (structureMap A U.obj).hom.IsIntegral :=
  sorry

/-- The structure sheaf `𝒪_X` is integral as an `𝒪_X`-algebra. -/
instance instIsIntegral_structureQcAlgebra {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsIntegral (structureQcAlgebra X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
