/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Base change of families of cycles on fibres

Base change is defined fibrewise by pulling back reduced point closures and
taking their associated cycles, with multiplicities extended additively.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FamilyOfCyclesOnFibres

/-- The degree-`r` cycle associated to the inverse image of a reduced point
closure under the canonical morphism between base-changed fibres. -/
noncomputable def fiberBaseChangeOfPoint {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (x : f.fiber (g s')) :
    CycleGroup ((pullback.snd f g).fiber s')
      ((pullback.snd f g).fiberRelativeDimensionFunction s') r :=
  @Scheme.IdealSheafData.associatedCycle ((pullback.snd f g).fiber s')
    (@instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType _ _ _
      (pullback.snd f g) (S'.fromSpecResidueField s')
      (isLocallyNoetherian_Spec.mpr
        (@UniversallyCatenaryRing.toIsNoetherian.{u, u} _ _ inferInstance)) inferInstance)
    ((Scheme.PointClosure.reducedStructure x).ideal.comap
      (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
        (IsPullback.of_hasPullback f g) s'))
    ((pullback.snd f g).fiberRelativeDimensionFunction s') r

/-- The base-change coefficient at a point is the sum of the original
coefficients times the multiplicities of the pulled-back reduced point closures. -/
noncomputable def fiberBaseChangeCoeff {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r)
    (x' : (pullback.snd f g).fiber s') : ℤ :=
  ∑ᶠ x : f.fiber (g s'),
    CycleGroup.toAlgebraicCycle (f.fiberRelativeDimensionFunction (g s')) r α x *
      (CycleGroup.toAlgebraicCycle ((pullback.snd f g).fiberRelativeDimensionFunction s') r
        (fiberBaseChangeOfPoint f g r s' x)) x'

/-- The coefficient function of fibrewise base change has locally finite support. -/
theorem fiberBaseChangeLocallyFiniteSupport {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    LocallyFiniteSupport (fiberBaseChangeCoeff f g r s' α) := sorry

/-- The algebraic cycle with the coefficients of fibrewise field-extension base change. -/
noncomputable def fiberBaseChangeCycle {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    AlgebraicCycle ((pullback.snd f g).fiber s') ℤ where
  toFun := fiberBaseChangeCoeff f g r s' α
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x' _ ↦
    fiberBaseChangeLocallyFiniteSupport f g r s' α x'

/-- The fibrewise base-change cycle is supported in dimension `r`. -/
theorem fiberBaseChangeCycle_mem_dimensionSubgroup {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    fiberBaseChangeCycle f g r s' α ∈
      AlgebraicCycle.dimensionSubgroup
        ((pullback.snd f g).fiberRelativeDimensionFunction s') r := sorry

/-- The degree-`r` cycle obtained by fibrewise field-extension base change. -/
noncomputable def fiberBaseChangeValue {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    CycleGroup ((pullback.snd f g).fiber s')
      ((pullback.snd f g).fiberRelativeDimensionFunction s') r :=
  ⟨fiberBaseChangeCycle f g r s' α,
    fiberBaseChangeCycle_mem_dimensionSubgroup f g r s' α⟩

/-- Fibrewise base change sends the zero cycle to zero. -/
theorem fiberBaseChangeValue_zero {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S') :
    fiberBaseChangeValue f g r s' 0 = 0 := sorry

/-- Fibrewise base change preserves addition of degree-`r` cycles. -/
theorem fiberBaseChangeValue_add {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (a b : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    fiberBaseChangeValue f g r s' (a + b) =
      fiberBaseChangeValue f g r s' a + fiberBaseChangeValue f g r s' b := sorry

/-- The additive homomorphism of degree-`r` cycles induced by field extension
along the canonical morphism between base-changed fibres. -/
noncomputable def fiberBaseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S') :
    CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r →+
      CycleGroup ((pullback.snd f g).fiber s')
        ((pullback.snd f g).fiberRelativeDimensionFunction s') r where
  toFun := fiberBaseChangeValue f g r s'
  map_zero' := fiberBaseChangeValue_zero f g r s'
  map_add' := fiberBaseChangeValue_add f g r s'

/-- Coefficients of the fibrewise base-change homomorphism are given by
the sum of coefficients times pulled-back point-closure multiplicities. -/
theorem fiberBaseChange_apply {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r)
    (x' : (pullback.snd f g).fiber s') :
    CycleGroup.toAlgebraicCycle ((pullback.snd f g).fiberRelativeDimensionFunction s') r
        (fiberBaseChange f g r s' α) x' =
      fiberBaseChangeCoeff f g r s' α x' := rfl

/-- The additive homomorphism of families of degree-`r` fibre cycles induced
by a morphism of bases. -/
noncomputable def baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    f.FiberCycleFamily r →+ (pullback.snd f g).FiberCycleFamily r :=
  AddMonoidHom.pi fun s' ↦ (fiberBaseChange f g r s').comp
    (Pi.evalAddMonoidHom
      (fun s ↦ CycleGroup (f.fiber s) (f.fiberRelativeDimensionFunction s) r) (g s'))

/-- Evaluation of family base change is fibrewise field-extension base change. -/
theorem baseChange_apply {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : f.FiberCycleFamily r) (s' : S') :
    baseChange f g r α s' = fiberBaseChange f g r s' (α (g s')) := rfl

/-- The canonical fibre map is an isomorphism when the base residue-field
map is an isomorphism.  This is used only to prove coefficient identities. -/
theorem isIso_baseChangeFiberMap {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S')
    (hκ : IsIso (g.residueFieldMap s')) :
    IsIso (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
      (IsPullback.of_hasPullback f g) s') := by
  letI := hκ
  exact (Scheme.Hom.isPullback_baseChangeFiberMap f g (pullback.fst f g)
    (pullback.snd f g) (IsPullback.of_hasPullback f g) s').isIso_fst_of_isIso

/-- Under a residue-field isomorphism the point-closure construction gives
the coefficient at the corresponding point, with its dimension filter. -/
theorem fiberBaseChangeCoeff_of_isIso {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (hκ : IsIso (g.residueFieldMap s'))
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r)
    (x' : (pullback.snd f g).fiber s') :
    fiberBaseChangeCoeff f g r s' α x' =
      if (pullback.snd f g).fiberRelativeDimensionFunction s' x' = r then
        α.1 (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
          (IsPullback.of_hasPullback f g) s' x') else 0 := by
  classical
  let j := Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
    (IsPullback.of_hasPullback f g) s'
  haveI : IsIso j := isIso_baseChangeFiberMap f g s' hκ
  haveI : IsLocallyNoetherian ((pullback.snd f g).fiber s') :=
    @instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType _ _ _
      (pullback.snd f g) (S'.fromSpecResidueField s')
      (isLocallyNoetherian_Spec.mpr
        (@UniversallyCatenaryRing.toIsNoetherian.{u, u} _ _ inferInstance)) inferInstance
  have hpoint (x : f.fiber (g s')) :
      (fiberBaseChangeOfPoint f g r s' x).1 x' =
        if x = j x' ∧ (pullback.snd f g).fiberRelativeDimensionFunction s' x' = r
          then 1 else 0 := by
    obtain ⟨y, rfl⟩ := j.homeomorph.surjective x
    change (((Scheme.PointClosure.reducedStructure (j y)).ideal.comap j).associatedCycle
      ((pullback.snd f g).fiberRelativeDimensionFunction s') r).1 x' =
        if j y = j x' ∧ (pullback.snd f g).fiberRelativeDimensionFunction s' x' = r
          then 1 else 0
    rw [Scheme.PointClosure.ideal_comap_of_isIso j y,
      Scheme.IdealSheafData.associatedCycle_pointClosure_apply]
    by_cases hy : y = x'
    · subst y
      simp only [eq_self, true_and]
    · have hj : j y ≠ j x' := fun h ↦ hy (j.homeomorph.injective h)
      simp [hy, Ne.symm hy, hj]
  change (∑ᶠ x, α.1 x * (fiberBaseChangeOfPoint f g r s' x).1 x') = _
  simp_rw [hpoint]
  rw [finsum_eq_single _ (j x')]
  · split_ifs <;> simp_all [j]
  · intro x hx
    simp [hx]

/-- Base change along a point-bijective morphism inducing residue-field
isomorphisms is bijective on families of nonnegative-dimensional fibre cycles
of a locally finite type morphism. -/
theorem baseChange_bijective {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    Function.Bijective (baseChange f g r) := sorry

/-- For a point bijection preserving residue fields, fibrewise base change
is exactly precomposition of coefficients along the canonical fibre map. -/
theorem fiberBaseChange_apply_of_bijective {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r)
    (x' : (pullback.snd f g).fiber s') :
    (fiberBaseChange f g r s' α).1 x' =
      α.1 (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
        (IsPullback.of_hasPullback f g) s' x') := by
  classical
  let j := Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
    (IsPullback.of_hasPullback f g) s'
  haveI : IsIso j := isIso_baseChangeFiberMap f g s' (hκ s')
  have hi : Function.Injective (fiberBaseChange f g r s') := by
    intro a b hab
    have hh : baseChange f g r (Pi.single (g s') a) =
        baseChange f g r (Pi.single (g s') b) := by
      funext t
      by_cases ht : t = s'
      · subst t
        simpa only [baseChange_apply, Pi.single_eq_same] using hab
      · have hgt : g t ≠ g s' := fun h ↦ ht (hg.injective h)
        simp only [baseChange_apply, Pi.single_eq_of_ne hgt, map_zero]
    have hs := congrFun ((baseChange_bijective f g hg hκ r).injective hh) (g s')
    simpa only [Pi.single_eq_same] using hs
  change fiberBaseChangeCoeff f g r s' α x' = α.1 (j x')
  rw [fiberBaseChangeCoeff_of_isIso f g r s' (hκ s')]
  by_cases hd : (pullback.snd f g).fiberRelativeDimensionFunction s' x' = r
  · simp [hd, j]
  simp only [if_neg hd]
  by_contra hx
  have hx' : α.1 (j x') ≠ 0 := Ne.symm hx
  have hdim := (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp α.2 (j x') hx'
  let c := CycleGroup.point (f.fiberRelativeDimensionFunction (g s')) r (j x') hdim
  have hc : fiberBaseChange f g r s' c = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y
    change fiberBaseChangeCoeff f g r s' c y = 0
    rw [fiberBaseChangeCoeff_of_isIso f g r s' (hκ s')]
    by_cases hy : y = x'
    · subst y
      simp only [if_neg hd]
    · have hjy : j y ≠ j x' := fun h ↦ hy (j.homeomorph.injective h)
      have hcy : c.1 (j y) = 0 := by
        simp [c, CycleGroup.point, Function.locallyFinsuppWithin.single_apply, hjy]
      change (if _ then c.1 (j y) else 0) = 0
      simp only [hcy, ite_self]
  have hc0 := hi (hc.trans (map_zero _).symm)
  have hcoeff := congrArg (fun a : CycleGroup _ _ r ↦ a.1 (j x')) hc0
  simpa [c, CycleGroup.point, Function.locallyFinsuppWithin.single_apply] using hcoeff

/-- Descend coefficients by summing over the points with the prescribed image
in `X`.  This definition does not choose a point or an inverse morphism. -/
def baseChangeInverseCoeff {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : (pullback.snd f g).FiberCycleFamily r)
    (s : S) (x : f.fiber s) : ℤ := by
  classical
  exact ∑ᶠ p : (Σ s' : S', (pullback.snd f g).fiber s'),
    if (pullback.fst f g) (((pullback.snd f g).fiberι p.1) p.2) = f.fiberι s x
      then (α p.1).1 p.2 else 0

private theorem fiberι_point {A B : Scheme.{u}} (h : A ⟶ B) (s : B) (x : h.fiber s) :
    h (h.fiberι s x) = s := by
  have hmem : h.fiberι s x ∈ h ⁻¹' {s} := by
    rw [← h.range_fiberι s]
    exact ⟨x, rfl⟩
  exact hmem

/-- The coefficient sum has a single term over each corresponding point.
All point-preimage arguments here remain inside this proposition proof. -/
theorem baseChangeInverseCoeff_at_image {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : (pullback.snd f g).FiberCycleFamily r)
    (s' : S') (x' : (pullback.snd f g).fiber s') :
    baseChangeInverseCoeff f g r α (g s')
      (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
        (IsPullback.of_hasPullback f g) s' x') = (α s').1 x' := by
  classical
  let T := fun p : (Σ t : S', (pullback.snd f g).fiber t) ↦
    (pullback.fst f g) ((pullback.snd f g).fiberι p.1 p.2)
  have hbase (p : Σ t : S', (pullback.snd f g).fiber t) : f (T p) = g p.1 := by
    have h := congrArg (fun k : pullback f g ⟶ S ↦
      k ((pullback.snd f g).fiberι p.1 p.2)) (pullback.condition (f := f) (g := g))
    simpa only [Scheme.Hom.comp_apply, fiberι_point] using h
  have hproj (t : S') (y : (pullback.snd f g).fiber t) :
      f.fiberι (g t) (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g)
        (pullback.snd f g) (IsPullback.of_hasPullback f g) t y) = T ⟨t, y⟩ := by
    have h := congrArg (fun k : (pullback.snd f g).fiber t ⟶ X ↦ k y)
      (Scheme.Hom.baseChangeFiberMap_fiberι f g
      (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g) t)
    exact h
  have hT : Function.Injective T := by
    rintro ⟨t, a⟩ ⟨u, b⟩ hab
    have htu : t = u := hg.injective ((hbase ⟨t, a⟩).symm.trans
      ((congrArg f hab).trans (hbase ⟨u, b⟩)))
    subst u
    apply congrArg (fun v : (pullback.snd f g).fiber t ↦
      (⟨t, v⟩ : Σ u : S', (pullback.snd f g).fiber u))
    let j := Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
      (IsPullback.of_hasPullback f g) t
    haveI : IsIso j := isIso_baseChangeFiberMap f g t (hκ t)
    apply j.homeomorph.injective
    apply (f.fiberι (g t)).isEmbedding.injective
    exact (hproj t a).trans (hab.trans (hproj t b).symm)
  unfold baseChangeInverseCoeff
  rw [finsum_eq_single _ (⟨s', x'⟩ : Σ t : S', (pullback.snd f g).fiber t)]
  · simp only [hproj s' x']
    exact if_pos rfl
  · intro p hp
    change (if T p = _ then _ else 0) = 0
    rw [hproj s' x']
    split_ifs with h
    · exact (hp (hT h)).elim
    · rfl

/-- The explicit coefficient descent is a left inverse to base change. -/
theorem baseChangeInverseCoeff_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : f.FiberCycleFamily r) (s : S) (x : f.fiber s) :
    baseChangeInverseCoeff f g r (baseChange f g r α) s x = (α s).1 x := by
  obtain ⟨s', rfl⟩ := hg.surjective s
  let j := Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
    (IsPullback.of_hasPullback f g) s'
  haveI : IsIso j := isIso_baseChangeFiberMap f g s' (hκ s')
  obtain ⟨x', rfl⟩ := j.homeomorph.surjective x
  change baseChangeInverseCoeff f g r (baseChange f g r α) (g s') (j x') =
    (α (g s')).1 (j x')
  rw [baseChangeInverseCoeff_at_image f g hg hκ]
  exact fiberBaseChange_apply_of_bijective f g hg hκ r s' (α (g s')) x'

/-- Descent along a point bijection with unchanged residue fields preserves
local finiteness of the coefficient support. -/
theorem baseChangeInverseCoeff_locallyFiniteSupport {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : (pullback.snd f g).FiberCycleFamily r) (s : S) :
    LocallyFiniteSupport (baseChangeInverseCoeff f g r α s) := by
  obtain ⟨β, rfl⟩ := (baseChange_bijective f g hg hκ r).surjective α
  have h : baseChangeInverseCoeff f g r (baseChange f g r β) s = (β s).1 := by
    funext x
    exact baseChangeInverseCoeff_baseChange f g hg hκ r β s x
  rw [h]
  exact (β s).1.locallyFiniteSupport

/-- The algebraic cycle given by the explicit descent coefficients. -/
def baseChangeInverseCycle {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (hg : Function.Bijective g)
    (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ)
    (α : (pullback.snd f g).FiberCycleFamily r) (s : S) :
    AlgebraicCycle (f.fiber s) ℤ where
  toFun := baseChangeInverseCoeff f g r α s
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    baseChangeInverseCoeff_locallyFiniteSupport f g hg hκ r α s x

/-- Descent through residue-field isomorphisms preserves fibre dimension. -/
theorem baseChangeInverseCycle_mem {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : (pullback.snd f g).FiberCycleFamily r) (s : S) :
    baseChangeInverseCycle f g hg hκ r α s ∈
      AlgebraicCycle.dimensionSubgroup (f.fiberRelativeDimensionFunction s) r := by
  obtain ⟨β, rfl⟩ := (baseChange_bijective f g hg hκ r).surjective α
  apply (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mpr
  intro x hx
  apply (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp (β s).2 x
  change baseChangeInverseCoeff f g r (baseChange f g r β) s x ≠ 0 at hx
  rwa [baseChangeInverseCoeff_baseChange f g hg hκ] at hx

/-- The inverse to point-bijective, residue-field-preserving base change,
computed by summing coefficients over the corresponding points.  The hypotheses
are used only in the support and dimension proofs, never to select data. -/
def baseChangeInverse {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (hg : Function.Bijective g)
    (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ)
    (α : (pullback.snd f g).FiberCycleFamily r) : f.FiberCycleFamily r :=
  fun s ↦ ⟨baseChangeInverseCycle f g hg hκ r α s,
    baseChangeInverseCycle_mem f g hg hκ r α s⟩

/-- The descent coefficient formula is exposed without unfolding proof fields. -/
theorem baseChangeInverse_apply {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyOfFiniteType f] (hg : Function.Bijective g)
    (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ)
    (α : (pullback.snd f g).FiberCycleFamily r) (s : S) (x : f.fiber s) :
    (baseChangeInverse f g hg hκ r α s).1 x = baseChangeInverseCoeff f g r α s x := rfl

/-- The coefficient formula is a left inverse to base change. -/
theorem baseChangeInverse_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : f.FiberCycleFamily r) :
    baseChangeInverse f g hg hκ r (baseChange f g r α) = α := by
  funext s
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact baseChangeInverseCoeff_baseChange f g hg hκ r α s x

/-- The coefficient formula is a right inverse to base change. -/
theorem baseChange_baseChangeInverse {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    (r : ℕ) (α : (pullback.snd f g).FiberCycleFamily r) :
    baseChange f g r (baseChangeInverse f g hg hκ r α) = α := by
  obtain ⟨β, rfl⟩ := (baseChange_bijective f g hg hκ r).surjective α
  rw [baseChangeInverse_baseChange]



end AlgebraicGeometry.FamilyOfCyclesOnFibres
