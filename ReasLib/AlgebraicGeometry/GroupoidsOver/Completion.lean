/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation

/-!
# Associated complete local algebra and formal object at a finite type point

The completed stalk `𝒪_{U,u0}^∧`, the canonical morphism `Spec(R) ⟶ U`, the
restriction of an object `x` of a groupoid fibration along that morphism, and
the formal object of positive maximal-adic truncations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The maximal-adic completion `𝒪_{U,u0}^∧` of the stalk of `U` at `u0`. -/
abbrev completionRing {U : Scheme.{u}} (u0 : U) : Type u :=
  AdicCompletion (maximalIdeal (U.presheaf.stalk u0)) (U.presheaf.stalk u0)

/-- `completionRing u0` is the `m_{u0}`-adic completion of `𝒪_{U,u0}`. -/
theorem completionRing_eq {U : Scheme.{u}} (u0 : U) :
    completionRing u0 =
      AdicCompletion (maximalIdeal (U.presheaf.stalk u0)) (U.presheaf.stalk u0) :=
  rfl

/-- The canonical morphism `Spec(𝒪_{U,u0}^∧) ⟶ U` induced by the completion map
on stalks. -/
def fromSpecCompletion {U : Scheme.{u}} (u0 : U) :
    Spec (CommRingCat.of (completionRing u0)) ⟶ U :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (U.presheaf.stalk u0) (completionRing u0))) ≫
    U.fromSpecStalk u0

/-- `fromSpecCompletion u0` is `Spec` of the completion map, followed by
`fromSpecStalk`. -/
theorem fromSpecCompletion_eq {U : Scheme.{u}} (u0 : U) :
    fromSpecCompletion u0 =
      Spec.map (CommRingCat.ofHom
          (algebraMap (U.presheaf.stalk u0) (completionRing u0))) ≫
        U.fromSpecStalk u0 :=
  rfl

/-- The residue-field point of `𝒪_{U,u0}^∧` remains locally of finite type over
`S`. -/
theorem completionResidue_locallyOfFiniteType {S U : Scheme.{u}}
    [IsLocallyNoetherian S] (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U)
    [IsFiniteTypePoint u0] [IsNoetherianRing (U.presheaf.stalk u0)] :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal (completionRing u0)))) ≫
        fromSpecCompletion u0 ≫ hU) := by
  let f := ResidueField.map (algebraMap (U.presheaf.stalk u0) (completionRing u0))
  have hf : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom f)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.FiniteType.of_surjective _ (AdicCompletion.residueField_map_bijective _).2)
  have h :
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal (completionRing u0)))) ≫
          fromSpecCompletion u0 =
        Spec.map (CommRingCat.ofHom f) ≫ U.fromSpecResidueField u0 := by
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk u0)
            (completionRing u0)) ≫ CommRingCat.ofHom
              (Ideal.Quotient.mk (maximalIdeal (completionRing u0)))) ≫
          U.fromSpecStalk u0 := (Spec.map_comp_assoc _ _ _).symm
      _ = Spec.map (U.residue u0 ≫ CommRingCat.ofHom f) ≫ U.fromSpecStalk u0 := rfl
      _ = _ := Spec.map_comp_assoc _ _ _
  rw [← Category.assoc, h]
  have hu : Scheme.Hom.FiniteType (U.fromSpecResidueField u0) := inferInstance
  exact @locallyOfFiniteType_comp _ _ _ _ _
    (@locallyOfFiniteType_comp _ _ _ _ _ hf hu.toLocallyOfFiniteType) inferInstance

/-- The completed stalk `𝒪_{U,u0}^∧` as a Noetherian complete local `S`-algebra,
with structure morphism `Spec(R) ⟶ U ⟶ S`. -/
def completionSAlgebra {S U : Scheme.{u}} [IsLocallyNoetherian S] (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0] :
    CompleteLocalSAlgebra S :=
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian hU
  have : IsNoetherianRing (U.presheaf.stalk u0) := inferInstance
  CompleteLocalSAlgebra.of (completionRing u0) (fromSpecCompletion u0 ≫ hU)
    (completionResidue_locallyOfFiniteType hU u0)

/-- `completionSAlgebra` packages the completed stalk and the composite
structure morphism `fromSpecCompletion u0 ≫ hU`. -/
theorem completionSAlgebra_spec {S U : Scheme.{u}} [IsLocallyNoetherian S]
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0] :
    (completionSAlgebra hU u0).carrier = completionRing u0 ∧
      (completionSAlgebra hU u0).toS = fromSpecCompletion u0 ≫ hU :=
  ⟨rfl, rfl⟩

/-- The restriction morphism `Spec(𝒪_{U,u0}^∧) ⟶ U` in `Over S`. -/
def fromSpecCompletionOverHom {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) :
    Over.mk (fromSpecCompletion u0 ≫ hU) ⟶ Over.mk hU :=
  Over.homMk (fromSpecCompletion u0) rfl

/-- The underlying scheme morphism of `fromSpecCompletionOverHom` is
`fromSpecCompletion`. -/
theorem fromSpecCompletionOverHom_left {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) :
    (fromSpecCompletionOverHom hU u0).left = fromSpecCompletion u0 :=
  rfl

/-- Restriction of `x` along `Spec(𝒪_{U,u0}^∧) ⟶ U`. -/
def restrictToCompletion {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) : X.total :=
  IsPreFibered.pullbackObj hx (fromSpecCompletionOverHom hU u0)

/-- The restricted object lies over `Spec(𝒪_{U,u0}^∧) ⟶ S`. -/
theorem restrictToCompletion_over {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    X.p.obj (restrictToCompletion hU x hx u0) =
      Over.mk (completionSAlgebra hU u0).toS :=
  IsPreFibered.pullbackObj_proj hx (fromSpecCompletionOverHom hU u0)

/-- The object `x` restricted to `Spec(𝒪_{U,u0}^∧)`, as a complete local object
of `X`. -/
def completeLocalObject {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    CompleteLocalObject X :=
  CompleteLocalObject.of (completionSAlgebra hU u0)
    (restrictToCompletion hU x hx u0)
    (IsPreFibered.pullbackObj_proj hx (fromSpecCompletionOverHom hU u0))

/-- `completeLocalObject` packages the completed-stalk algebra and the
restriction of `x`. -/
theorem completeLocalObject_spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    (completeLocalObject hU x hx u0).base = completionSAlgebra hU u0 ∧
      (completeLocalObject hU x hx u0).object =
        restrictToCompletion hU x hx u0 :=
  ⟨rfl, rfl⟩

/-- Formal object of `X` over `𝒪_{U,u0}^∧` associated to `x` restricted to
`Spec(𝒪_{U,u0}^∧)` along its positive maximal-adic truncations. -/
def associatedFormalObject {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    FormalObject X :=
  FormalObject.restriction (completeLocalObject hU x hx u0)

/-- `associatedFormalObject` is restriction of `completeLocalObject` along
truncations `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
theorem associatedFormalObject_eq_restriction {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (u0 : U) [IsFiniteTypePoint u0] :
    associatedFormalObject hU x hx u0 =
      FormalObject.restriction (completeLocalObject hU x hx u0) :=
  rfl

/-- The complete local `S`-algebra of the associated formal object is the
completed stalk. -/
theorem associatedFormalObject_base {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    (associatedFormalObject hU x hx u0).base = completionSAlgebra hU u0 :=
  rfl

/-- The underlying ring of the associated formal object is the completed stalk
`𝒪_{U,u0}^∧`. -/
theorem associatedFormalObject_carrier {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    (associatedFormalObject hU x hx u0).base.carrier = completionRing u0 :=
  rfl

end AlgebraicGeometry.GroupoidsOver
