/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials

/-!
# Restriction of relative differentials of algebraic spaces

Relative differentials restrict along an étale-vertical commutative square to the
relative differentials of the upper morphism. For schemes, this restriction agrees
with the usual sheaf of relative differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- In a commutative square of algebraic spaces with étale vertical arrows, restriction
of the relative differentials of the lower morphism is isomorphic to the relative
differentials of the upper morphism. -/
@[stacks 04CU]
theorem restrict_relativeDifferentials
    {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : U ⟶ X) (b : V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a ψ f b) :
    IsIsomorphic (Modules.restrict (relativeDifferentials f) a) (relativeDifferentials ψ) :=
  sorry

/-- In a commutative square with étale vertical arrows and schemes in the upper row,
the restricted relative differentials of the lower morphism agree, on the underlying
scheme, with the usual sheaf of relative differentials of the upper morphism. -/
@[stacks 04CU]
theorem restrict_relativeDifferentials_ofOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b) :
    IsIsomorphic
      ((Modules.restrictToScheme U).obj (Modules.restrict (relativeDifferentials f) a))
      (RingedSpace.Hom.differentials ψ.left.toShHom) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
