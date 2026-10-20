/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.Realization
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion.Compatibility
import StacksCheckRecall

/-! # Upgrading versal rings to morphisms and compatible comparisons -/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Remark 107.2.9 (Upgrading versal rings)
A versal ring is realized by an actual morphism from its spectrum; the
comparisons below lift to actual morphisms, up to invertible 2-arrows.
-/
@[stacks 0DR1] #check (AlgebraicGeometry.AlgebraicStack.exists_realizesVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A],
    ∃ x : CompleteLocalObject X, RealizesVersalRing x0 A x)

#check (AlgebraicGeometry.CompleteLocalSAlgebra.Hom.congr :
  ∀ {S : Scheme.{u}}
    {R R' T T' : CompleteLocalSAlgebra S} (hR : R = R') (hT : T = T')
    (φ : CompleteLocalSAlgebra.Hom R T),
    CompleteLocalSAlgebra.Hom R' T')

#check (AlgebraicGeometry.CompleteLocalSAlgebra.Hom.congr_eq :
  ∀ {S : Scheme.{u}}
    {R R' T T' : CompleteLocalSAlgebra S} (hR : R = R')
    (hT : T = T') (φ : CompleteLocalSAlgebra.Hom R T),
    CompleteLocalSAlgebra.Hom.congr hR hT φ = hR ▸ hT ▸ φ)

#check (AlgebraicGeometry.AlgebraicStack.exists_realizesVersalFormalObject :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ : FormalObject X) [GroupoidsOver.FormalObject.IsVersal ξ] (m : StageOneMarking x0 ξ),
    ∃ (x : CompleteLocalObject X) (h : x.base = ξ.base),
      RealizesVersalRing x0 ξ.base x ∧
        ∃ e : FormalObject.restriction x ≅ ξ,
          CompleteLocalSAlgebra.Hom.congr h rfl
            (GroupoidsOver.FormalObject.Hom.base e.hom) = CompleteLocalSAlgebra.Hom.id ξ.base)

#check (AlgebraicGeometry.AlgebraicStack.exists_isPowerSeriesExtension_compatible :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A']
    (x x' : CompleteLocalObject X)
    (hx : RealizesVersalRing x0 A x) (hx' : RealizesVersalRing x0 A' x')
    (m : StageOneMarking x0 (FormalObject.restriction x))
    (m' : StageOneMarking x0 (FormalObject.restriction x')),
    (∃ φ : CompleteLocalSAlgebra.Hom A A',
      IsPowerSeriesExtension φ ∧
        ∃ f : CompleteLocalObject.Hom x x',
          CompleteLocalSAlgebra.Hom.congr hx.1 hx'.1 (CompleteLocalObject.baseHom f) = φ ∧
            m.iso.hom ≫ (FormalObject.approximationMap f).app 0 = m'.iso.hom) ∨
    (∃ φ : CompleteLocalSAlgebra.Hom A' A,
      IsPowerSeriesExtension φ ∧
        ∃ f : CompleteLocalObject.Hom x' x,
          CompleteLocalSAlgebra.Hom.congr hx'.1 hx.1 (CompleteLocalObject.baseHom f) = φ ∧
            m'.iso.hom ≫ (FormalObject.approximationMap f).app 0 = m.iso.hom))

#check (AlgebraicGeometry.AlgebraicStack.exists_isVersalRing_restrict_compatible :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (l : Type u) [Field l] [Algebra x0.K l] [Module.Finite x0.K l]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (x : CompleteLocalObject X) (hx : RealizesVersalRing x0 A x),
    ∃ A' : CompleteLocalSAlgebra S,
      IsVersalRing (x0.restrict l) A' ∧
        ∃ (x' : CompleteLocalObject X) (hx' : RealizesVersalRing (x0.restrict l) A' x')
          (φ : CompleteLocalSAlgebra.Hom A' A),
          φ.hom.formally_smooth_for_adic (maximalIdeal A'.carrier) ∧
            φ.InducesResidueExtension x0.K l x0.structureHom
              (x0.restrict l).structureHom ∧
              ∃ f : CompleteLocalObject.Hom x' x,
                CompleteLocalSAlgebra.Hom.congr hx'.1 hx.1
                  (CompleteLocalObject.baseHom f) = φ)

#check (AlgebraicGeometry.AlgebraicStack.realizesVersalRing_completeLocalObject :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0],
    RealizesVersalRing (FieldValuedPoint.induced hU x hx u0)
      (completionSAlgebra hU u0) (completeLocalObject hU x hx u0))

#check (AlgebraicGeometry.AlgebraicStack.exists_smooth_realizesVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (xA : CompleteLocalObject X) (hxA : RealizesVersalRing x0 A xA) (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)],
    ∃ (W : SmoothFiniteTypeObject x0.structureHom x0.fiberObj)
      (φ : CompleteLocalSAlgebra.Hom A (completionSAlgebra W.toS W.u0)),
      Function.Bijective φ.hom ∧
        ∃ f : CompleteLocalObject.Hom xA (completeLocalObject W.toS W.object W.over_obj W.u0),
          CompleteLocalSAlgebra.Hom.congr hxA.1 rfl (CompleteLocalObject.baseHom f) = φ)

#check (AlgebraicGeometry.AlgebraicStack.yonedaOfObject_completeLocalObject :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    Nonempty
      (yonedaOfObject (completeLocalObject hU x hx u0).base.toS
          (completeLocalObject hU x hx u0).object
          (completeLocalObject hU x hx u0).over_obj ≅
        overMap (fromSpecCompletionOverHom hU u0) ≫ yonedaOfObject hU x hx))

#check (AlgebraicGeometry.AlgebraicStack.isObjectComparison_formallyHomotopic :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {ξ η : FormalObject X} [GroupoidsOver.FormalObject.IsVersal ξ] [GroupoidsOver.FormalObject.IsVersal η]
    (mξ : StageOneMarking x0 ξ) (mη : StageOneMarking x0 η)
    {φ ψ : CompleteLocalSAlgebra.Hom η.base ξ.base}
    (hφ : IsPointedObjectComparison x0 ξ η mξ mη φ)
    (hψ : IsPointedObjectComparison x0 ξ η mξ mη ψ),
    FormallyHomotopic φ ψ)
