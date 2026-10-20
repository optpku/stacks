/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpenRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Induced

/-! # Versality and smooth neighbourhoods of algebraic stacks -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

open GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

/-- Versality of an object at a finite type point over a locally Noetherian base
is equivalent to smoothness of its residue-field deformation functors, versality
of its completed-stalk formal object, and smoothness on an open neighbourhood
of the point. -/
theorem isVersalAt_tfae {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    List.TFAE
      [IsVersalAt hU x hx u0,
        (∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
          [Algebra Λ (residueFieldType u0)]
          [Module.Finite Λ (residueFieldType u0)]
          (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
          [IsOpenImmersion openImmersion]
          (h_factor :
            Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
                openImmersion =
              fromResidueField u0 ≫ hU),
          BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor)),
        GroupoidsOver.FormalObject.IsVersal (associatedFormalObject hU x hx u0),
        ∃ U' : U.Opens, u0 ∈ U' ∧
          Groupoids.Hom.Smooth (restrictToOpen hU x hx U')] :=
  sorry

/-- Versality at a finite type point is equivalent to smoothness of the
2-Yoneda 1-morphism after restriction to some open neighbourhood of that
point. -/
theorem isVersalAt_iff_exists_isSmooth_restrict {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∃ U' : U.Opens, u0 ∈ U' ∧
        Groupoids.Hom.Smooth (restrictToOpen hU x hx U') :=
  sorry

/-- The completed stalk at a finite type point where an object is versal is
a versal ring at the induced residue-field point. -/
instance instIsVersalRing_completionSAlgebra {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0] :
    IsVersalRing (FieldValuedPoint.induced hU x hx u0)
      (completionSAlgebra hU u0) :=
  sorry


end AlgebraicGeometry.AlgebraicStack
