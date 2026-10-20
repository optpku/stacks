/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Point

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

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.SubspacePoint.hom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S},
    SubspacePoint f U → (yoneda.obj U ⟶ functor f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.SubspacePoint.hom_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S}
    (p : SubspacePoint f U),
    yonedaEquiv (SubspacePoint.hom p) = (functor_obj_equiv f U).symm (PointQuot.mk p))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.SubspacePoint.hom_comp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S}
    (p : SubspacePoint f U), p.hom ≫ FinitePart.hom f = p.a)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.SubspacePoint.hom_rel :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S}
    {p q : SubspacePoint f U}, SubspacePoint.Rel f U p q → SubspacePoint.hom p = SubspacePoint.hom q)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.relativelyRepresentable_hom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U : Over S}
    (p : SubspacePoint f U), yoneda.relativelyRepresentable (SubspacePoint.hom p))

end AlgebraicGeometry.AlgebraicSpace.FinitePart

