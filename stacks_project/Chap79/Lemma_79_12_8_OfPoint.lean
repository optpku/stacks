/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap79.Lemma_79_12_7_Hom

/-!
# Induced morphism from a finite-part pair

A finite-part pair `(a, Z)` over a scheme `U` determines a morphism of functors
`U ⟶ (X/Y)_fin`, the Yoneda transpose of the subspace class of the pair.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The morphism `U ⟶ (X/Y)_fin` induced by a finite-part pair `(a, Z)` over a
scheme `U`. -/
def Point.hom {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    yoneda.obj U ⟶ functor f :=
  yonedaEquiv.symm ((functor_obj_equiv f U).symm (PointQuot.mk p))

/-- Evaluating `Point.hom p` recovers the subspace class of the pair. -/
theorem Point.hom_eq {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    yonedaEquiv (Point.hom p) = (functor_obj_equiv f U).symm (PointQuot.mk p) :=
  sorry

/-- The induced morphism `U ⟶ (X/Y)_fin` lies over `a : U ⟶ Y`. -/
theorem Point.hom_comp {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    p.hom ≫ FinitePart.hom f = p.a :=
  sorry

/-- Subspace-equivalent pairs induce the same morphism `U ⟶ (X/Y)_fin`. -/
theorem Point.hom_rel {f : X ⟶ Y} {U : Over S} {p q : Point f U}
    (h : Point.Rel f U p q) : Point.hom p = Point.hom q :=
  sorry

/-- The induced morphism `U ⟶ (X/Y)_fin` is representable by schemes. -/
theorem relativelyRepresentable_hom {f : X ⟶ Y} {U : Over S} (p : Point f U) :
    yoneda.relativelyRepresentable (Point.hom p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart

