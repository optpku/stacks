/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Pushforward of families of `r`-cycles on fibres along a thickening over a
common base is a bijection. -/
theorem pushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (fun α : fX.FiberCycleFamily r ↦ pushforward fX' i hc α) := sorry

/-- Pull back the coefficients of a fibre cycle along a thickening.  This is
an actual coefficient formula, without choosing preimages of cycles. -/
def thickeningInverseCoeff {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    (hc : i ≫ fX' = fX) (r : ℕ) (α : fX'.FiberCycleFamily r)
    (s : S) (x : fX.fiber s) : ℤ :=
  (α s).1 (pushforwardFiberMap fX fX' i hc s x)

/-- At the image of a point of an injective morphism, pushforward has just
one possible summand. -/
private theorem mapHom_coeff_at_image {A B : Scheme.{u}} (j : A ⟶ B)
    [QuasiCompact j] (hj : Function.Injective j) (dA : A → ℤ) (dB : B → ℤ)
    (r : ℕ) (c : CycleGroup A dA r) (x : A) :
    (CycleGroup.mapHom j dA dB r c).1 (j x) =
      c.1 x * (AlgebraicCycle.mapCoeff j dA dB x : ℤ) := by
  classical
  change (∑ᶠ z ∈ j ⁻¹' {j x},
    c.1 z * (AlgebraicCycle.mapCoeff j dA dB z : ℤ)) = _
  have h : j ⁻¹' {j x} = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hj.eq_iff
  rw [h, finsum_mem_singleton]

/-- A thickening has residue-field degree one, so pulling back the
coefficients of its pushforward recovers each original coefficient. -/
theorem thickeningInverseCoeff_pushforward {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX.FiberCycleFamily r) (s : S) (x : fX.fiber s) :
    thickeningInverseCoeff fX fX' i hc r (pushforward fX' i hc α) s x =
      (α s).1 x := by
  classical
  let j := pushforwardFiberMap fX fX' i hc s
  let dA := fX.fiberDimensionFunction s
  let dB := fX'.fiberDimensionFunction s
  have hproj : j ≫ fX'.fiberι s = fX.fiberι s ≫ i := by
    change j ≫ CategoryTheory.Limits.pullback.fst fX' (S.fromSpecResidueField s) =
      CategoryTheory.Limits.pullback.fst fX (S.fromSpecResidueField s) ≫ i
    dsimp only [j, pushforwardFiberMap, Scheme.Hom.fiberMap]
    exact CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hj : Function.Injective j := by
    intro a b hab
    apply (fX.fiberι s).isEmbedding.injective
    apply i.isEmbedding.injective
    have ha := congrArg (fun k : fX.fiber s ⟶ X' ↦ k a) hproj
    have hb := congrArg (fun k : fX.fiber s ⟶ X' ↦ k b) hproj
    simpa only [Scheme.Hom.comp_apply] using
      ha.symm.trans ((congrArg (fX'.fiberι s) hab).trans hb)
  have hb : Function.Bijective (CycleGroup.mapHom j dA dB r) := by
    have h := pushforward_bijective fX fX' i hc r
    constructor
    · intro a b hab
      have hh : pushforward fX' i hc (Pi.single s a) =
          pushforward fX' i hc (Pi.single s b) := by
        funext t
        by_cases ht : t = s
        · subst t
          simpa only [pushforward, Pi.single_eq_same] using hab
        · simp [pushforward, Pi.single_eq_of_ne ht]
      have hsame := congrFun (h.injective hh) s
      simpa only [Pi.single_eq_same] using hsame
    · intro c
      obtain ⟨β, hβ⟩ := h.surjective (Pi.single s c)
      refine ⟨β s, ?_⟩
      have hs := congrFun hβ s
      simpa only [pushforward, Pi.single_eq_same] using hs
  change (CycleGroup.mapHom j dA dB r (α s)).1 (j x) = (α s).1 x
  rw [mapHom_coeff_at_image j hj]
  by_cases hx : (α s).1 x = 0
  · simp [hx]
  have hdim : dA x = (r : ℤ) :=
    (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp (α s).2 x hx
  let c := CycleGroup.point dA r x hdim
  have hw : AlgebraicCycle.mapCoeff j dA dB x ≠ 0 := by
    intro hw
    have hzero : CycleGroup.mapHom j dA dB r c = 0 := by
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro y
      change (∑ᶠ z ∈ j ⁻¹' {y},
        c.1 z * (AlgebraicCycle.mapCoeff j dA dB z : ℤ)) = 0
      apply finsum_eq_zero_of_forall_eq_zero
      intro z
      by_cases hzx : z = x
      · subst z
        simp [hw]
      · have hc0 : c.1 z = 0 := by
          simp [c, CycleGroup.point, Function.locallyFinsuppWithin.single_apply, hzx]
        simp [hc0]
    have hc0 := hb.injective (hzero.trans (map_zero _).symm)
    have hc1 := congrArg (fun a : CycleGroup _ dA r ↦ a.1 x) hc0
    simpa [c, CycleGroup.point, Function.locallyFinsuppWithin.single_apply] using hc1
  have hweights : dA x = dB (j x) := by
    by_contra hne
    exact hw (by simp [AlgebraicCycle.mapCoeff, hne])
  let c' := CycleGroup.point dB r (j x) (hweights.symm.trans hdim)
  obtain ⟨β, hβ⟩ := hb.surjective c'
  have hcoeff := congrArg (fun a : CycleGroup _ dB r ↦ a.1 (j x)) hβ
  have heq : β.1 x * (AlgebraicCycle.mapCoeff j dA dB x : ℤ) = 1 := by
    rw [mapHom_coeff_at_image j hj] at hcoeff
    simpa [c', CycleGroup.point, Function.locallyFinsuppWithin.single_apply] using hcoeff
  have hdvd : (AlgebraicCycle.mapCoeff j dA dB x : ℤ) ∣ 1 :=
    ⟨β.1 x, by simpa only [mul_comm] using heq.symm⟩
  have hnat : AlgebraicCycle.mapCoeff j dA dB x ∣ 1 := by exact_mod_cast hdvd
  simp [Nat.dvd_one.mp hnat]

/-- Coefficient pullback along a thickening has locally finite support. -/
theorem thickeningInverseCoeff_locallyFiniteSupport {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) (s : S) :
    LocallyFiniteSupport (thickeningInverseCoeff fX fX' i hc r α s) := by
  obtain ⟨β, rfl⟩ := (pushforward_bijective fX fX' i hc r).surjective α
  have h : thickeningInverseCoeff fX fX' i hc r (pushforward fX' i hc β) s =
      (β s).1 := by
    funext x
    exact thickeningInverseCoeff_pushforward fX fX' i hc r β s x
  rw [h]
  exact (β s).1.locallyFiniteSupport

/-- The cycle obtained by pulling back coefficients along a thickening. -/
def thickeningInverseCycle {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) (s : S) : AlgebraicCycle (fX.fiber s) ℤ where
  toFun := thickeningInverseCoeff fX fX' i hc r α s
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    thickeningInverseCoeff_locallyFiniteSupport fX fX' i hc r α s x

/-- A thickening does not change the dimension of the point supporting a coefficient. -/
theorem thickeningInverseCycle_mem {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) (s : S) :
    thickeningInverseCycle fX fX' i hc r α s ∈
      AlgebraicCycle.dimensionSubgroup (fX.fiberDimensionFunction s) r := by
  obtain ⟨β, rfl⟩ := (pushforward_bijective fX fX' i hc r).surjective α
  apply (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mpr
  intro x hx
  apply (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp (β s).2 x
  change thickeningInverseCoeff fX fX' i hc r (pushforward fX' i hc β) s x ≠ 0 at hx
  rwa [thickeningInverseCoeff_pushforward] at hx

/-- The inverse of thickening pushforward, defined by precomposition of coefficients. -/
def thickeningInverse {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) : fX.FiberCycleFamily r :=
  fun s ↦ ⟨thickeningInverseCycle fX fX' i hc r α s,
    thickeningInverseCycle_mem fX fX' i hc r α s⟩

/-- Coefficients of the inverse are the target coefficients at the image point. -/
theorem thickeningInverse_apply {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) (s : S) (x : fX.fiber s) :
    (thickeningInverse fX fX' i hc r α s).1 x =
      (α s).1 (pushforwardFiberMap fX fX' i hc s x) := rfl

/-- Coefficient pullback is a left inverse to thickening pushforward. -/
theorem thickeningInverse_pushforward {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) (α : fX.FiberCycleFamily r) :
    thickeningInverse fX fX' i hc r (pushforward fX' i hc α) = α := by
  funext s
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact thickeningInverseCoeff_pushforward fX fX' i hc r α s x

/-- Coefficient pullback is a right inverse to thickening pushforward. -/
theorem pushforward_thickeningInverse {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S)
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) (α : fX'.FiberCycleFamily r) :
    pushforward fX' i hc (thickeningInverse fX fX' i hc r α) = α := by
  obtain ⟨β, rfl⟩ := (pushforward_bijective fX fX' i hc r).surjective α
  rw [thickeningInverse_pushforward]

/-- The explicit coefficient inverse preserves the relative-cycle condition. -/
theorem isRelative_thickeningInverse {X X' S : Scheme.{u}}
    (fX : X ⟶ S) (fX' : X' ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fX'] (i : X ⟶ X')
    [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : fX'.FiberCycleFamily r) (hα : IsRelative α) :
    IsRelative (thickeningInverse fX fX' i hc r α) := by
  apply (isRelative_iff_pushforward fX fX' i hc r _).mpr
  simpa only [pushforward_thickeningInverse] using hα

/-- Thickening pushforward as an equivalence with an explicit coefficient inverse. -/
def groupThickeningEquiv {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fX']
    (i : X ⟶ X') [IsThickening i] (hc : i ≫ fX' = fX) (r : ℕ) :
    group fX r ≃+ group fX' r where
  toFun := groupPushforward fX fX' i hc r
  invFun α := ⟨thickeningInverse fX fX' i hc r α.1,
    isRelative_thickeningInverse fX fX' i hc r α.1 α.2⟩
  left_inv α := Subtype.ext (thickeningInverse_pushforward fX fX' i hc r α.1)
  right_inv α := Subtype.ext (pushforward_thickeningInverse fX fX' i hc r α.1)
  map_add' := (groupPushforward fX fX' i hc r).map_add

/-- A thickening between schemes locally of finite type over a locally
Noetherian base induces a bijection on relative `r`-cycles. -/
@[stacks 0H5E]
theorem groupPushforward_bijective {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsThickening i]
    (hc : i ≫ fX' = fX) (r : ℕ) :
    Function.Bijective (groupPushforward fX fX' i hc r) :=
  (groupThickeningEquiv fX fX' i hc r).bijective

end AlgebraicGeometry.RelativeCycle
