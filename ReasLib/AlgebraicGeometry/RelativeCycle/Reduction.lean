/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Transport
public import ReasLib.AlgebraicGeometry.RelativeCycle.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The comparison morphism from the reduction of `X` to the pullback of `f`
along the reduction inclusion of `S`. -/
def reductionComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.reduction X ⟶ pullback f (Scheme.reductionι S) :=
  pullback.lift (Scheme.reductionι X) (Scheme.reductionMap f) (Scheme.reductionMap_reductionι f).symm

/-- The comparison morphism projects to the reduction of `f`. -/
theorem reductionComparison_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    reductionComparison f ≫ pullback.snd f (Scheme.reductionι S) =
      Scheme.reductionMap f :=
  by
  simp only [reductionComparison, pullback.lift_snd]

/-- The comparison from `X_red` to `X ×_S S_red` is a thickening: a surjective
closed immersion, not in general an isomorphism. -/
instance instIsThickening_reductionComparison {X S : Scheme.{u}} (f : X ⟶ S) :
    IsThickening (reductionComparison f) :=
  sorry

/-- Reduction of a locally finite type morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_reductionMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (Scheme.reductionMap f) :=
  sorry

/-- The reduction inclusion induces residue-field isomorphisms. -/
theorem isIso_reductionι_residueFieldMap (X : Scheme.{u})
    (x : Scheme.reduction X) :
    IsIso ((Scheme.reductionι X).residueFieldMap x) :=
  sorry

/-- Closed-immersion pushforward of an effective relative `r`-cycle remains
effective. -/
theorem effectivePushforward_mem {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) (α : effective fX r) :
    pushforward fX' i hc (α : fX.FiberCycleFamily r) ∈ effective fX' r :=
  sorry

/-- Pushforward along a closed immersion over a common base is additive on effective cycles. -/
def effectivePushforward {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fX']
    (i : X ⟶ X') [IsClosedImmersion i] (hc : i ≫ fX' = fX) (r : ℕ) :
    effective fX r →+ effective fX' r :=
  ((AddMonoidHom.pi fun s : S ↦
    (CycleGroup.mapHom (pushforwardFiberMap fX fX' i hc s)
      (fX.fiberDimensionFunction s) (fX'.fiberDimensionFunction s) r).comp
        (Pi.evalAddMonoidHom
          (fun t : S ↦ CycleGroup (fX.fiber t) (fX.fiberDimensionFunction t) r) s)).comp
    (effective fX r).subtype).codRestrict (effective fX' r)
      (effectivePushforward_mem fX fX' i hc r)

/-- The underlying fibrewise family of `effectivePushforward` is family-level
pushforward. -/
theorem effectivePushforward_apply {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) (α : effective fX r) :
    (effectivePushforward fX fX' i hc r α : fX'.FiberCycleFamily r) =
      pushforward fX' i hc (α : fX.FiberCycleFamily r) :=
  rfl

/-- Pulling back coefficients along a thickening preserves nonnegativity. -/
theorem isEffective_thickeningInverse {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) (hα : IsEffective α) :
    IsEffective (thickeningInverse fX fX' i hc r α) := by
  apply (isEffective_iff _).mpr
  intro s x
  exact ((isEffective_iff _).mp hα) s (pushforwardFiberMap fX fX' i hc s x)

/-- Effective thickening pushforward with its explicit coefficient inverse. -/
def effectiveThickeningEquiv {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fX']
    (i : X ⟶ X') [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) :
    effective fX r ≃+ effective fX' r where
  toFun := effectivePushforward fX fX' i hc r
  invFun α := ⟨thickeningInverse fX fX' i hc r α.1,
    isRelative_thickeningInverse fX fX' i hc r α.1 α.2.1,
    isEffective_thickeningInverse fX fX' i hc r α.1 α.2.2⟩
  left_inv α := Subtype.ext (thickeningInverse_pushforward fX fX' i hc r α.1)
  right_inv α := Subtype.ext (pushforward_thickeningInverse fX fX' i hc r α.1)
  map_add' := (effectivePushforward fX fX' i hc r).map_add

/-- A sum of nonnegative coefficients over matching fibre points is nonnegative. -/
theorem isEffective_baseChangeInverse {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : (pullback.snd f g).FiberCycleFamily r) (hα : IsEffective α) :
    IsEffective (FamilyOfCyclesOnFibres.baseChangeInverse f g hg hκ r α) := by
  classical
  apply (isEffective_iff _).mpr
  intro s x
  change 0 ≤ FamilyOfCyclesOnFibres.baseChangeInverseCoeff f g r α s x
  unfold FamilyOfCyclesOnFibres.baseChangeInverseCoeff
  apply finsum_nonneg
  intro p
  split_ifs
  · exact ((isEffective_iff _).mp hα) p.1 p.2
  · exact le_rfl

/-- Effective base change with an explicit inverse sum of matching coefficients. -/
def effectiveBaseChangeEquiv {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g]
    (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    effective f r ≃+ effective (pullback.snd f g) r where
  toFun := effectiveBaseChange f g r
  invFun α := ⟨FamilyOfCyclesOnFibres.baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1,
    isRelative_baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1 α.2.1,
    isEffective_baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1 α.2.2⟩
  left_inv α := Subtype.ext
    (FamilyOfCyclesOnFibres.baseChangeInverse_baseChange f g g.isHomeomorph.bijective hκ r α.1)
  right_inv α := Subtype.ext
    (FamilyOfCyclesOnFibres.baseChange_baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1)
  map_add' := (effectiveBaseChange f g r).map_add


/-- The inverse of pushforward along a thickening preserves effectiveness. -/
theorem isEffective_of_isEffective_pushforward {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) {r : ℕ} {α : fX.FiberCycleFamily r}
    (hα : IsRelative α) :
    IsEffective (pushforward fX' i hc α) → IsEffective α := by
  intro h
  have h' := isEffective_thickeningInverse fX fX' i hc r _ h
  simpa only [thickeningInverse_pushforward] using h'

/-- Pushforward of effective relative `r`-cycles along a thickening is
bijective. -/
theorem effectivePushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsThickening i]
    (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (effectivePushforward fX fX' i hc r) :=
  (effectiveThickeningEquiv fX fX' i hc r).bijective

/-- Base change of effective relative cycles along the reduction inclusion is
bijective. -/
theorem effectiveBaseChange_reductionι_bijective {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    Function.Bijective (effectiveBaseChange f (Scheme.reductionι S) r) :=
  (effectiveBaseChangeEquiv f (Scheme.reductionι S)
    (fun s' ↦ isIso_reductionι_residueFieldMap S s') r).bijective

/-- Identification `z(X/S, r) ≃+ z(X_red / S_red, r)` of relative cycle groups,
as base change along `reductionι` inverted through pushforward along the
thickening `reductionComparison`. -/
def groupReductionEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    group f r ≃+ group (Scheme.reductionMap f) r :=
  (groupBaseChangeEquiv f (Scheme.reductionι S)
    (fun s' ↦ isIso_reductionι_residueFieldMap S s') r).trans
    (groupThickeningEquiv (Scheme.reductionMap f)
      (pullback.snd f (Scheme.reductionι S))
      (reductionComparison f) (reductionComparison_snd f) r).symm

/-- Pushforward along `reductionComparison` recovers base change along
`reductionι` from `groupReductionEquiv`. -/
theorem groupReductionEquiv_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) (α : group f r) :
    groupPushforward (Scheme.reductionMap f) (pullback.snd f (Scheme.reductionι S))
        (reductionComparison f) (reductionComparison_snd f) r
        (groupReductionEquiv f r α) =
      groupBaseChange f (Scheme.reductionι S) r α :=
  (groupThickeningEquiv (Scheme.reductionMap f)
    (pullback.snd f (Scheme.reductionι S))
    (reductionComparison f) (reductionComparison_snd f) r).apply_symm_apply _

/-- Identification `z^{eff}(X/S, r) ≃+ z^{eff}(X_red / S_red, r)` of effective
relative cycles, as effective base change along `reductionι` inverted through
effective pushforward along the thickening `reductionComparison`. -/
def effectiveReductionEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ) :
    effective f r ≃+ effective (Scheme.reductionMap f) r :=
  (effectiveBaseChangeEquiv f (Scheme.reductionι S)
    (fun s' ↦ isIso_reductionι_residueFieldMap S s') r).trans
    (effectiveThickeningEquiv (Scheme.reductionMap f)
      (pullback.snd f (Scheme.reductionι S))
      (reductionComparison f) (reductionComparison_snd f) r).symm

/-- Effective pushforward along `reductionComparison` recovers effective base
change along `reductionι` from `effectiveReductionEquiv`. -/
theorem effectiveReductionEquiv_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : effective f r) :
    effectivePushforward (Scheme.reductionMap f)
        (pullback.snd f (Scheme.reductionι S))
        (reductionComparison f) (reductionComparison_snd f) r
        (effectiveReductionEquiv f r α) =
      effectiveBaseChange f (Scheme.reductionι S) r α :=
  (effectiveThickeningEquiv (Scheme.reductionMap f)
    (pullback.snd f (Scheme.reductionι S))
    (reductionComparison f) (reductionComparison_snd f) r).apply_symm_apply _

end AlgebraicGeometry.RelativeCycle
