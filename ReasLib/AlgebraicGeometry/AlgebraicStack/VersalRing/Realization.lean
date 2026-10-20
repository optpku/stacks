/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Induced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Restriction
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.ResidueExtension
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.AlgebraicStack
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothFiniteTypeObject
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.Smooth.Adic.Basic

/-! # Effective realizations and compatible comparisons of versal rings -/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- A complete local object realizes a versal ring at a field-valued point when
its base is that ring and its own formal restriction is versal and compatible
with the point at the residue stage. -/
def RealizesVersalRing (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X) : Prop :=
  x.base = A ∧ StageOneCompatible x0 (FormalObject.restriction x) ∧
    GroupoidsOver.FormalObject.IsVersal (FormalObject.restriction x)

/-- Realization is the prescribed-base condition together with residue-stage
compatibility and versality of the actual formal restriction. -/
theorem RealizesVersalRing.iff (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X) :
    RealizesVersalRing x0 A x ↔
      x.base = A ∧ StageOneCompatible x0 (FormalObject.restriction x) ∧
        GroupoidsOver.FormalObject.IsVersal (FormalObject.restriction x) := Iff.rfl

/-- A ring admitting a complete local realization at a field-valued point is
a versal ring at that point. -/
instance RealizesVersalRing.toIsVersalRing [AlgebraicStack X]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S)
    [Fact (∃ x : CompleteLocalObject X, RealizesVersalRing x0 A x)] :
    IsVersalRing x0 A := sorry

/-- A marked versal formal object at a finite-type field-valued point of a
locally finite type algebraic stack has a complete local realization whose
formal isomorphism induces the identity on the prescribed base. -/
theorem exists_realizesVersalFormalObject [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ : FormalObject X) [GroupoidsOver.FormalObject.IsVersal ξ] (m : StageOneMarking x0 ξ) :
    ∃ (x : CompleteLocalObject X) (h : x.base = ξ.base),
      RealizesVersalRing x0 ξ.base x ∧
        ∃ e : FormalObject.restriction x ≅ ξ,
          CompleteLocalSAlgebra.Hom.congr h rfl
            (GroupoidsOver.FormalObject.Hom.base e.hom) = CompleteLocalSAlgebra.Hom.id ξ.base :=
  sorry

/-- Every versal ring at a finite-type field-valued point of a locally finite
type algebraic stack admits a complete local realization. -/
theorem exists_realizesVersalRing [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    ∃ x : CompleteLocalObject X, RealizesVersalRing x0 A x :=
  sorry

/-- Two specified marked realizations at the same finite-type point have a
finite-variable power-series comparison in one direction, lifted by an actual
local morphism whose residue-stage map preserves their markings. -/
theorem exists_isPowerSeriesExtension_compatible [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A']
    (x x' : CompleteLocalObject X)
    (hx : RealizesVersalRing x0 A x) (hx' : RealizesVersalRing x0 A' x')
    (m : StageOneMarking x0 (FormalObject.restriction x))
    (m' : StageOneMarking x0 (FormalObject.restriction x')) :
    (∃ φ : CompleteLocalSAlgebra.Hom A A',
      IsPowerSeriesExtension φ ∧
        ∃ f : CompleteLocalObject.Hom x x',
          CompleteLocalSAlgebra.Hom.congr hx.1 hx'.1 (CompleteLocalObject.baseHom f) = φ ∧
            m.iso.hom ≫ (FormalObject.approximationMap f).app 0 = m'.iso.hom) ∨
    (∃ φ : CompleteLocalSAlgebra.Hom A' A,
      IsPowerSeriesExtension φ ∧
        ∃ f : CompleteLocalObject.Hom x' x,
          CompleteLocalSAlgebra.Hom.congr hx'.1 hx.1 (CompleteLocalObject.baseHom f) = φ ∧
            m'.iso.hom ≫ (FormalObject.approximationMap f).app 0 = m.iso.hom) :=
  sorry

/-- A finite residue-field extension of a specified versal realization admits
a realization over the extended field and an actual local arrow to the original
object, inducing that extension and formally smooth in the target adic topology. -/
theorem exists_isVersalRing_restrict_compatible [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (l : Type u) [Field l] [Algebra x0.K l] [Module.Finite x0.K l]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (x : CompleteLocalObject X) (hx : RealizesVersalRing x0 A x) :
    ∃ A' : CompleteLocalSAlgebra S,
      IsVersalRing (x0.restrict l) A' ∧
        ∃ (x' : CompleteLocalObject X) (hx' : RealizesVersalRing (x0.restrict l) A' x')
          (φ : CompleteLocalSAlgebra.Hom A' A),
          φ.hom.formally_smooth_for_adic (maximalIdeal A'.carrier) ∧
            φ.InducesResidueExtension x0.K l x0.structureHom
              (x0.restrict l).structureHom ∧
              ∃ f : CompleteLocalObject.Hom x' x,
                CompleteLocalSAlgebra.Hom.congr hx'.1 hx.1
                  (CompleteLocalObject.baseHom f) = φ :=
  sorry

/-- The canonical completed-stalk restriction of an object versal at a
finite-type point realizes a versal ring at its induced field-valued point. -/
theorem realizesVersalRing_completeLocalObject [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0] :
    RealizesVersalRing (FieldValuedPoint.induced hU x hx u0)
      (completionSAlgebra hU u0) (completeLocalObject hU x hx u0) :=
  sorry

/-- If the base stalk is a G-ring, a specified versal realization admits a
smooth finite-type chart with the prescribed residue field and a bijective
completion map lifted by an actual arrow to the canonical completed-stalk object. -/
theorem exists_smooth_realizesVersalRing [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (xA : CompleteLocalObject X) (hxA : RealizesVersalRing x0 A xA) (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)] :
    ∃ (W : SmoothFiniteTypeObject x0.structureHom x0.fiberObj)
      (φ : CompleteLocalSAlgebra.Hom A (completionSAlgebra W.toS W.u0)),
      Function.Bijective φ.hom ∧
        ∃ f : CompleteLocalObject.Hom xA (completeLocalObject W.toS W.object W.over_obj W.u0),
          CompleteLocalSAlgebra.Hom.congr hxA.1 rfl (CompleteLocalObject.baseHom f) = φ :=
  sorry

end AlgebraicGeometry.AlgebraicStack

