/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.RingTheory.Regular.GRing

/-! # Finite-type versal approximations of formal objects -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

/-- Canonical morphism `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U`. -/
def fromSpecStalkPow {U : Scheme.{u}} (u0 : U) (n : ℕ) :
    Spec (CommRingCat.of
        (U.presheaf.stalk u0 ⧸ maximalIdeal (U.presheaf.stalk u0) ^ (n + 1))) ⟶
      U :=
  Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal (U.presheaf.stalk u0) ^ (n + 1)))) ≫
    U.fromSpecStalk u0

/-- `fromSpecStalkPow` is `Spec` of the quotient map, followed by `fromSpecStalk`. -/
theorem fromSpecStalkPow_eq {U : Scheme.{u}} (u0 : U) (n : ℕ) :
    fromSpecStalkPow u0 n =
      Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (maximalIdeal (U.presheaf.stalk u0) ^ (n + 1)))) ≫
        U.fromSpecStalk u0 :=
  rfl

/-- Restriction morphism `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U` in `Over S`. -/
def fromSpecStalkPowOverHom {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) (n : ℕ) :
    Over.mk (fromSpecStalkPow u0 n ≫ hU) ⟶ Over.mk hU :=
  Over.homMk (fromSpecStalkPow u0 n) rfl

/-- The underlying scheme morphism of `fromSpecStalkPowOverHom` is
`fromSpecStalkPow`. -/
theorem fromSpecStalkPowOverHom_left {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U)
    (n : ℕ) :
    (fromSpecStalkPowOverHom hU u0 n).left = fromSpecStalkPow u0 n :=
  rfl

/-- Restriction of `x` along `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ U`. -/
def restrictToStalkPow {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ) :
    X.total :=
  IsPreFibered.pullbackObj hx (fromSpecStalkPowOverHom hU u0 n)

/-- `restrictToStalkPow` is the chosen cartesian pullback along
`fromSpecStalkPowOverHom`. -/
theorem restrictToStalkPow_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ) :
    restrictToStalkPow hU x hx u0 n =
      IsPreFibered.pullbackObj hx (fromSpecStalkPowOverHom hU u0 n) :=
  rfl

/-- The restricted object lies over `Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1}) ⟶ S`. -/
theorem restrictToStalkPow_over {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (n : ℕ) :
    X.p.obj (restrictToStalkPow hU x hx u0 n) =
      Over.mk (fromSpecStalkPow u0 n ≫ hU) :=
  IsPreFibered.pullbackObj_proj hx (fromSpecStalkPowOverHom hU u0 n)

/-- Finite-type approximation data of a formal object: a finite type scheme
`U ⟶ S`, a finite type point `u0` with residue field `κ(R)`, and an object `x`
over `U` which is versal at `u0` and whose associated formal object is
isomorphic to `ξ`. The positive truncations are indexed by `n + 1`. -/
structure ApproximateVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} (ξ : FormalObject X) where
  /-- Approximating scheme of finite type over `S`. -/
  U : Scheme.{u}
  /-- Structure morphism `U ⟶ S`. -/
  toS : U ⟶ S
  /-- The structure morphism is of finite type. -/
  finiteType : Scheme.Hom.FiniteType toS
  /-- Finite type point of `U` at which the approximating object is versal. -/
  u0 : U
  /-- The chosen point is of finite type. -/
  isFiniteTypePoint : IsFiniteTypePoint u0
  /-- Identification `κ(u0) ≃+* κ(R)` of residue fields. -/
  residueIso : residueFieldType u0 ≃+* ResidueField ξ.base.carrier
  /-- `Spec(κ(u0)) ⟶ S` agrees with `Spec(κ(R)) ⟶ S` after `residueIso`. -/
  residueIso_over :
    fromResidueField u0 ≫ toS =
      Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
        FormalObject.residueToS ξ
  /-- Approximating object of `X`. -/
  object : X.total
  /-- The approximating object lies over `U ⟶ S`. -/
  over_obj : X.p.obj object = Over.mk toS
  /-- The approximating object is versal at the chosen point. -/
  isVersalAt :
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : Scheme.Hom.FiniteType toS := finiteType
    IsVersalAt toS object over_obj u0
  /-- The formal object of `x` over `𝒪_{U,u0}^∧` is isomorphic to `ξ`. -/
  associatedIso :
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : Scheme.Hom.FiniteType toS := finiteType
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : IsFiniteTypePoint u0 := isFiniteTypePoint
    associatedFormalObject toS object over_obj u0 ≅ ξ

namespace ApproximateVersal

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
variable {ξ : FormalObject X}

/-- Package finite-type approximation data of a formal object. -/
def of (U : Scheme.{u}) (toS : U ⟶ S) [Scheme.Hom.FiniteType toS] (u0 : U)
    [IsFiniteTypePoint u0]
    (residueIso : residueFieldType u0 ≃+* ResidueField ξ.base.carrier)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫
          FormalObject.residueToS ξ)
    (object : X.total) (over_obj : X.p.obj object = Over.mk toS)
    [IsVersalAt toS object over_obj u0]
    (associatedIso : associatedFormalObject toS object over_obj u0 ≅ ξ) :
    ApproximateVersal ξ where
  U := U
  toS := toS
  finiteType := inferInstance
  u0 := u0
  isFiniteTypePoint := inferInstance
  residueIso := residueIso
  residueIso_over := residueIso_over
  object := object
  over_obj := over_obj
  isVersalAt := inferInstance
  associatedIso := associatedIso

/-- Conditions encoded by approximation data: finite type structure
morphism, finite type point, residue-field identification over `S`, object over
`U`, versality at `u0`, and isomorphism of associated formal objects. -/
theorem spec (W : ApproximateVersal ξ) :
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : Scheme.Hom.FiniteType W.toS := W.finiteType
    -- Local instance justification (proof-local temporary data): the canonical pointwise-versality and completed-stalk APIs take finiteness proofs as class arguments; these bindings pass exactly the immutable proofs stored in this explicit approximation record, with no new inference rule.
    letI : IsFiniteTypePoint W.u0 := W.isFiniteTypePoint
    Scheme.Hom.FiniteType W.toS ∧
      IsFiniteTypePoint W.u0 ∧
        (fromResidueField W.u0 ≫ W.toS =
          Spec.map (CommRingCat.ofHom W.residueIso.symm.toRingHom) ≫
            FormalObject.residueToS ξ) ∧
          X.p.obj W.object = Over.mk W.toS ∧
            IsVersalAt W.toS W.object W.over_obj W.u0 ∧
              Nonempty
                (associatedFormalObject W.toS W.object W.over_obj W.u0 ≅ ξ) :=
  ⟨W.finiteType, W.isFiniteTypePoint, W.residueIso_over, W.over_obj,
    W.isVersalAt, ⟨W.associatedIso⟩⟩

/-- The approximating object restricted to
`Spec(𝒪_{U,u0} ⧸ m_{u0}^{n+1})` is isomorphic to `ξ.objects n` over `S`. -/
theorem exists_restrictIso (W : ApproximateVersal ξ) (n : ℕ) :
    ∃ (e : restrictToStalkPow W.toS W.object W.over_obj W.u0 n ≅ ξ.objects n)
      (f : Over.mk (fromSpecStalkPow W.u0 n ≫ W.toS) ⟶ ξ.base.stageOver n),
      X.p.IsHomLift f e.hom := by
  letI : Scheme.Hom.FiniteType W.toS := W.finiteType
  letI : IsFiniteTypePoint W.u0 := W.isFiniteTypePoint
  letI : IsLocallyNoetherian W.U := LocallyOfFiniteType.isLocallyNoetherian W.toS
  let A : Type u := W.U.presheaf.stalk W.u0
  let B := completionRing W.u0
  -- Evaluation identifies the positive truncations of the stalk and its completion.
  have hker : RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) (n + 1)).toRingHom =
      maximalIdeal B ^ (n + 1) := by
    ext z
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
      ← Submodule.restrictScalars_mem A
        ((maximalIdeal A ^ (n + 1)).map (algebraMap A B)),
      ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing]
    change (Ideal.quotientEquivAlgOfEq A
      (show (maximalIdeal A ^ (n + 1) • ⊤ : Ideal A) =
        maximalIdeal A ^ (n + 1) by simp))
          (AdicCompletion.eval (maximalIdeal A) A (n + 1) z) = 0 ↔ _
    exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq A _).injective
  let eB : (B ⧸ maximalIdeal B ^ (n + 1)) ≃ₐ[A] A ⧸ maximalIdeal A ^ (n + 1) :=
    (Ideal.quotientEquivAlgOfEq A hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (AdicCompletion.surjective_evalₐ (maximalIdeal A) (n + 1)))
  let eSpec := Scheme.Spec.mapIso eB.toRingEquiv.toCommRingCatIso.op
  let y := completeLocalObject W.toS W.object W.over_obj W.u0
  have hfactor :
      fromSpecStalkPow W.u0 n = eSpec.hom ≫
        (y.base.truncationToSpec n ≫ fromSpecCompletion W.u0) := by
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ W.U.fromSpecStalk W.u0 =
      Spec.map (CommRingCat.ofHom eB.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ W.U.fromSpecStalk W.u0))
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
  let eOver : Over.mk (fromSpecStalkPow W.u0 n ≫ W.toS) ≅ y.base.stageOver n :=
    Over.isoMk eSpec (by
      change eSpec.hom ≫ (y.base.truncationToSpec n ≫
        (fromSpecCompletion W.u0 ≫ W.toS)) = fromSpecStalkPow W.u0 n ≫ W.toS
      simp only [← Category.assoc, ← hfactor]
      rfl)
  have hOver : fromSpecStalkPowOverHom W.toS W.u0 n =
      eOver.hom ≫ (y.base.truncationOverHom n ≫
        fromSpecCompletionOverHom W.toS W.u0) := by
    apply Over.OverMorphism.ext
    exact hfactor
  -- Both restrictions are cartesian lifts of the same map after this base isomorphism.
  let φ := FormalObject.restrictionHom y n ≫
    IsPreFibered.pullbackMap W.over_obj (fromSpecCompletionOverHom W.toS W.u0)
  have hpullback {R T : Over S} {a : X.total} (ha : X.p.obj a = T) (f : R ⟶ T) :
      X.p.IsStronglyCartesian f (IsPreFibered.pullbackMap ha f) :=
    @IsFibered.isStronglyCartesian_of_isCartesian _ _ _ _ X.p inferInstance _ _ f _ _
      (IsPreFibered.pullbackMap ha f) (IsPreFibered.pullbackMap.IsCartesian ha f)
  have hφ : X.p.IsStronglyCartesian (y.base.truncationOverHom n ≫
      fromSpecCompletionOverHom W.toS W.u0) φ :=
    @IsStronglyCartesian.comp _ _ _ _ X.p _ _ _ _ _ _ _ _ _ _
      (FormalObject.restrictionHom_isStronglyCartesian y n)
      (hpullback W.over_obj (fromSpecCompletionOverHom W.toS W.u0))
  let e₁ : restrictToStalkPow W.toS W.object W.over_obj W.u0 n ≅
      (associatedFormalObject W.toS W.object W.over_obj W.u0).objects n :=
    @IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ X.p _ _ _ _ _ _ _ _ eOver hOver φ
      (IsPreFibered.pullbackMap W.over_obj (fromSpecStalkPowOverHom W.toS W.u0 n))
      hφ (hpullback W.over_obj (fromSpecStalkPowOverHom W.toS W.u0 n))
  -- Compose with the given formal isomorphism at stage `n`.
  let e₂ : (associatedFormalObject W.toS W.object W.over_obj W.u0).objects n ≅
      ξ.objects n :=
    { hom := W.associatedIso.hom.app n
      inv := W.associatedIso.inv.app n
      hom_inv_id := congrArg (fun f ↦ f.app n) W.associatedIso.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.app n) W.associatedIso.inv_hom_id }
  let e := e₁ ≪≫ e₂
  refine ⟨e, eqToHom (restrictToStalkPow_over W.toS W.object W.over_obj W.u0 n).symm ≫
    X.p.map e.hom ≫ eqToHom (ξ.over_obj n), ?_⟩
  exact IsHomLift.of_fac X.p _ e.hom
    (restrictToStalkPow_over W.toS W.object W.over_obj W.u0 n) (ξ.over_obj n) rfl

end ApproximateVersal

/-- A versal effective formal object over a locally Noetherian scheme admits a
finite-type approximation versal at a finite type point with the same residue
field and isomorphic associated formal object, if the local ring at the residue
image is a G-ring and the structure morphism is limit preserving on objects. -/
theorem nonempty_approximateVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    (ξ : FormalObject X) (s : S)
    (hs : ξ.base.toS (closedPoint ξ.base.carrier) = s)
    [IsGRing (S.presheaf.stalk s)] [FormalObject.IsEffective ξ]
    (h_versal : FormalObject.IsVersalOnObjects ξ) :
    Nonempty (ApproximateVersal ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
