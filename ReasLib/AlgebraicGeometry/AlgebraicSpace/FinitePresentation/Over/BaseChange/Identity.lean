/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over.BaseChange

/-!
# Identity base change for algebraic spaces of finite presentation

Base change along an identity morphism has canonical identity comparison
isomorphisms, both for algebraic spaces and for the finite-presentation subcategory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

/-- Base change along an identity morphism preserves the functor of points. -/
theorem baseChange_id_functorOfPoints {T : Scheme.{u}} (X : AlgebraicSpace T) :
    (AlgebraicSpace.baseChange (𝟙 T) X).functorOfPoints = X.functorOfPoints :=
  sorry

/-- Base change of algebraic spaces along an identity morphism is isomorphic to
the identity functor. -/
def baseChangeFunctor_id (T : Scheme.{u}) :
    AlgebraicSpace.baseChangeFunctor (𝟙 T) ≅ 𝟭 (AlgebraicSpace T) :=
  NatIso.ofComponents
    (fun X ↦ isoOfFunctorOfPoints (eqToIso (baseChange_id_functorOfPoints X)))
    sorry

/-- Base change along the identity morphism of schemes is isomorphic to the
identity functor on algebraic spaces of finite presentation. -/
def baseChange_id (T : Scheme.{u}) :
    baseChange (𝟙 T) ≅ 𝟭 (FinitePresentationOver T) :=
  NatIso.ofComponents
    (fun X ↦
      { hom := homMk ((baseChangeFunctor_id T).hom.app X.obj)
        inv := homMk ((baseChangeFunctor_id T).inv.app X.obj)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
