/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Diagonal

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
def SubspacePoint.hom {f : X ⟶ Y} {U : Over S} (p : SubspacePoint f U) :
    yoneda.obj U ⟶ functor f :=
  yonedaEquiv.symm ((functor_obj_equiv f U).symm (PointQuot.mk p))

/-- Evaluating `SubspacePoint.hom p` recovers the subspace class of the pair. -/
theorem SubspacePoint.hom_eq {f : X ⟶ Y} {U : Over S} (p : SubspacePoint f U) :
    yonedaEquiv (SubspacePoint.hom p) = (functor_obj_equiv f U).symm (PointQuot.mk p) :=
  sorry

/-- The induced morphism `U ⟶ (X/Y)_fin` lies over `a : U ⟶ Y`. -/
theorem SubspacePoint.hom_comp {f : X ⟶ Y} {U : Over S} (p : SubspacePoint f U) :
    p.hom ≫ FinitePart.hom f = p.a :=
  sorry

/-- Subspace-equivalent pairs induce the same morphism `U ⟶ (X/Y)_fin`. -/
theorem SubspacePoint.hom_rel {f : X ⟶ Y} {U : Over S} {p q : SubspacePoint f U}
    (h : SubspacePoint.Rel f U p q) : SubspacePoint.hom p = SubspacePoint.hom q :=
  sorry

/-- The induced morphism `U ⟶ (X/Y)_fin` is representable by schemes. -/
theorem relativelyRepresentable_hom {f : X ⟶ Y} {U : Over S} (p : SubspacePoint f U) :
    yoneda.relativelyRepresentable (SubspacePoint.hom p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
