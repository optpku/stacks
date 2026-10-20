/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion

/-! # Completed-stalk restrictions and their formal objects

Compatibility checks for the canonical completed-stalk constructions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidsOver.completionRing :
  ∀ {U : Scheme.{u}} (u0 : U),
    Type u)

#check (AlgebraicGeometry.GroupoidsOver.completionRing_eq :
  ∀ {U : Scheme.{u}} (u0 : U),
    completionRing u0 =
      AdicCompletion (maximalIdeal (U.presheaf.stalk u0)) (U.presheaf.stalk u0))

#check (AlgebraicGeometry.GroupoidsOver.fromSpecCompletion :
  ∀ {U : Scheme.{u}} (u0 : U),
    Spec (CommRingCat.of (completionRing u0)) ⟶ U)

#check (AlgebraicGeometry.GroupoidsOver.fromSpecCompletion_eq :
  ∀ {U : Scheme.{u}} (u0 : U),
    fromSpecCompletion u0 =
      Spec.map (CommRingCat.ofHom
          (algebraMap (U.presheaf.stalk u0) (completionRing u0))) ≫
        U.fromSpecStalk u0)

#check (AlgebraicGeometry.GroupoidsOver.completionResidue_locallyOfFiniteType :
  ∀ {S U : Scheme.{u}}
    [IsLocallyNoetherian S] (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U)
    [IsFiniteTypePoint u0] [IsNoetherianRing (U.presheaf.stalk u0)],
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal (completionRing u0)))) ≫
        fromSpecCompletion u0 ≫ hU))

#check (AlgebraicGeometry.GroupoidsOver.completionSAlgebra :
  ∀ {S U : Scheme.{u}} [IsLocallyNoetherian S] (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0],
    CompleteLocalSAlgebra S)

#check (AlgebraicGeometry.GroupoidsOver.completionSAlgebra_spec :
  ∀ {S U : Scheme.{u}} [IsLocallyNoetherian S]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0],
    (completionSAlgebra hU u0).carrier = completionRing u0 ∧
      (completionSAlgebra hU u0).toS = fromSpecCompletion u0 ≫ hU)

#check (AlgebraicGeometry.GroupoidsOver.fromSpecCompletionOverHom :
  ∀ {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U),
    Over.mk (fromSpecCompletion u0 ≫ hU) ⟶ Over.mk hU)

#check (AlgebraicGeometry.GroupoidsOver.fromSpecCompletionOverHom_left :
  ∀ {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U),
    (fromSpecCompletionOverHom hU u0).left = fromSpecCompletion u0)

#check (AlgebraicGeometry.GroupoidsOver.restrictToCompletion :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U),
    X.total)

#check (AlgebraicGeometry.GroupoidsOver.restrictToCompletion_over :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    X.p.obj (restrictToCompletion hU x hx u0) =
      Over.mk (completionSAlgebra hU u0).toS)

#check (AlgebraicGeometry.GroupoidsOver.completeLocalObject :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    CompleteLocalObject X)

#check (AlgebraicGeometry.GroupoidsOver.completeLocalObject_spec :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    (completeLocalObject hU x hx u0).base = completionSAlgebra hU u0 ∧
      (completeLocalObject hU x hx u0).object =
        restrictToCompletion hU x hx u0)

#check (AlgebraicGeometry.GroupoidsOver.associatedFormalObject :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    FormalObject X)

#check (AlgebraicGeometry.GroupoidsOver.associatedFormalObject_eq_restriction :
  ∀ {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) [IsFiniteTypePoint u0],
    associatedFormalObject hU x hx u0 =
      FormalObject.restriction (completeLocalObject hU x hx u0))

#check (AlgebraicGeometry.GroupoidsOver.associatedFormalObject_base :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    (associatedFormalObject hU x hx u0).base = completionSAlgebra hU u0)

#check (AlgebraicGeometry.GroupoidsOver.associatedFormalObject_carrier :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    (associatedFormalObject hU x hx u0).base.carrier = completionRing u0)
