/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Local fibre dimensions under base change

This leaf records local-ring dimension and residue-field transcendence-degree
formulas for a pullback square of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiberDimension

private theorem ringKrullDim_fiberStalkAt_eq_natCast
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    ringKrullDim (fiberStalkAt f x) =
      ((((ringKrullDim (fiberStalkAt f x)).unbotD 0).toNat : ℕ) : WithBot ℕ∞) := by
  letI : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  letI : FiniteRingKrullDim (fiberStalkAt f x) := inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := fiberStalkAt f x))
  have hdt : d ≠ ⊤ := by
    intro hdt
    apply ringKrullDim_ne_top (R := fiberStalkAt f x)
    rw [← hd, hdt]
    rfl
  lift d to ℕ using hdt
  simp [← hd]

private theorem eq_natCast_sub_of_add_eq
    (a : WithBot ℕ∞) (m n : ℕ) (ha : 0 ≤ a)
    (h : a + (m : WithBot ℕ∞) = n) :
    a = ((n - m : ℕ) : WithBot ℕ∞) := by
  have hmn : (m : WithBot ℕ∞) ≤ n := by
    calc
      (m : WithBot ℕ∞) = 0 + m := (zero_add _).symm
      _ ≤ a + m := add_le_add ha le_rfl
      _ = n := h
  have hmn' : m ≤ n := by exact_mod_cast hmn
  apply (ENat.WithBot.add_natCast_cancel (c := m)).mp
  rw [h, ← Nat.cast_add, Nat.sub_add_cancel hmn']

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced map between fixed fibres, added to the original fixed-fibre stalk
dimension, is the pullback fixed-fibre stalk dimension. -/
theorem ringKrullDim_baseChangeFiberStalkAt_add_eq_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        ringKrullDim (fiberStalkAt f (g' x')) =
      ringKrullDim (fiberStalkAt f' x') := sorry

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced map between fixed fibres is the difference of the two fixed-fibre
stalk dimensions. -/
theorem ringKrullDim_baseChangeFiberStalkAt_eq_sub_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') =
      ((ringKrullDim (fiberStalkAt f' x')).unbotD 0).toNat -
        ((ringKrullDim (fiberStalkAt f (g' x'))).unbotD 0).toNat := by
  letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hpb inferInstance
  apply eq_natCast_sub_of_add_eq
  · show 0 ≤ ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x')
    exact ringKrullDim_nonneg_of_nontrivial
  · show ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        ((((ringKrullDim (fiberStalkAt f (g' x'))).unbotD 0).toNat : ℕ) : WithBot ℕ∞) =
      ((((ringKrullDim (fiberStalkAt f' x')).unbotD 0).toNat : ℕ) : WithBot ℕ∞)
    rw [← ringKrullDim_fiberStalkAt_eq_natCast f (g' x'),
      ← ringKrullDim_fiberStalkAt_eq_natCast f' x']
    exact ringKrullDim_baseChangeFiberStalkAt_add_eq_of_isPullback f g g' f' hpb x'

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced fixed-fibre map, added to the upstairs residue-field transcendence
degree, is the residue-field transcendence degree at the image point. -/
theorem baseChangeFiberStalkDim_add_trdeg_eq
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        f'.residueFieldTrdegAt x' =
      f.residueFieldTrdegAt (g' x') := by
  letI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hpb inferInstance
  have hdim := fiberDimensionAt_eq_of_isPullback f g g' f' hpb x'
  rw [at_eq_stalk_add_trdeg f' x', at_eq_stalk_add_trdeg f (g' x')] at hdim
  have hsum : ringKrullDim (fiberStalkAt f (g' x')) +
        (ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
          f'.residueFieldTrdegAt x') =
      ringKrullDim (fiberStalkAt f (g' x')) + f.residueFieldTrdegAt (g' x') := by
    calc
      _ = (ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
          ringKrullDim (fiberStalkAt f (g' x'))) + f'.residueFieldTrdegAt x' := by
        ac_rfl
      _ = ringKrullDim (fiberStalkAt f' x') + f'.residueFieldTrdegAt x' := by
        rw [ringKrullDim_baseChangeFiberStalkAt_add_eq_of_isPullback f g g' f' hpb x']
      _ = _ := hdim
  rw [ringKrullDim_fiberStalkAt_eq_natCast f (g' x')] at hsum
  exact ENat.WithBot.natCast_add_cancel.mp hsum

/-- In a pullback square, the dimension of the local ring of the fibre of the
induced fixed-fibre map is the difference of the corresponding residue-field
transcendence degrees. -/
theorem baseChangeFiberStalkDim_eq_trdeg_sub
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') =
      f.residueFieldTrdegAt (g' x') - f'.residueFieldTrdegAt x' := by
  apply eq_natCast_sub_of_add_eq
  · show 0 ≤ ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x')
    exact ringKrullDim_nonneg_of_nontrivial
  · show ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        f'.residueFieldTrdegAt x' = f.residueFieldTrdegAt (g' x')
    exact baseChangeFiberStalkDim_add_trdeg_eq f g g' f' hpb x'

/-- Pullback does not decrease the Krull dimension of the local ring at the
distinguished point of a fixed scheme-theoretic fibre. -/
theorem ringKrullDim_fiberStalkAt_le_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    ringKrullDim (fiberStalkAt f (g' x')) ≤ ringKrullDim (fiberStalkAt f' x') := by
  calc
    _ = 0 + ringKrullDim (fiberStalkAt f (g' x')) := (zero_add _).symm
    _ ≤ ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
        ringKrullDim (fiberStalkAt f (g' x')) :=
      add_le_add ringKrullDim_nonneg_of_nontrivial le_rfl
    _ = _ := ringKrullDim_baseChangeFiberStalkAt_add_eq_of_isPullback f g g' f' hpb x'

/-- The residue-field transcendence degree at a point of a pullback is at
most that at its image in the original scheme. -/
theorem residueFieldTrdegAt_le_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') :
    f'.residueFieldTrdegAt x' ≤ f.residueFieldTrdegAt (g' x') := by
  have hle : (f'.residueFieldTrdegAt x' : WithBot ℕ∞) ≤
      f.residueFieldTrdegAt (g' x') := by
    calc
      _ = 0 + (f'.residueFieldTrdegAt x' : WithBot ℕ∞) := (zero_add _).symm
      _ ≤ ringKrullDim (baseChangeFiberStalkAt f g g' f' hpb x') +
          f'.residueFieldTrdegAt x' :=
        add_le_add ringKrullDim_nonneg_of_nontrivial le_rfl
      _ = _ := baseChangeFiberStalkDim_add_trdeg_eq f g g' f' hpb x'
  exact_mod_cast hle

private theorem exists_point_ringKrullDim_stalk_eq_zero (F : Scheme.{u}) (z : F) :
    ∃ η : F, ringKrullDim (F.presheaf.stalk η) = 0 := by
  let Z := irreducibleComponent z
  have hZ := irreducibleComponent_mem_irreducibleComponents z
  have hη : IsGenericPoint (isIrreducible_irreducibleComponent (x := z)).genericPoint Z :=
    IsIrreducible.isGenericPoint_genericPoint _ isClosed_irreducibleComponent
  refine ⟨(isIrreducible_irreducibleComponent (x := z)).genericPoint, ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, ← WithBot.coe_zero, WithBot.coe_inj]
  apply Order.coheight_eq_zero.mpr
  intro t ht
  have hsub : Z ⊆ closure ({t} : Set F) := by
    rw [← hη.def]
    exact (Scheme.le_iff_specializes.mp ht).closure_subset
  have hback : closure ({t} : Set F) ⊆ Z :=
    hZ.2 isIrreducible_singleton.closure hsub
  exact Scheme.le_iff_specializes.mpr (hη.specializes (hback (subset_closure (by simp))))

private theorem ringKrullDim_fiberStalkAt_fiberι
    {A B : Scheme.{u}} (m : A ⟶ B) (b : B) (z : m.fiber b) :
    ringKrullDim (fiberStalkAt m (m.fiberι b z)) =
      ringKrullDim ((m.fiber b).presheaf.stalk z) := by
  generalize ha : m.fiberι b z = a
  have hb : m a = b := by
    rw [← ha]
    exact (m.fiberHomeo b z).property
  subst b
  have hz : m.asFiber a = z := by
    apply (m.fiberι (m a)).isEmbedding.injective
    simpa using ha.symm
  change ringKrullDim ((m.fiber (m a)).presheaf.stalk (m.asFiber a)) = _
  rw [hz]

private theorem exists_point_fiberStalkAt_eq_zero
    {A B : Scheme.{u}} (m : A ⟶ B) (a : A) :
    ∃ a' : A, m a' = m a ∧ ringKrullDim (fiberStalkAt m a') = 0 := by
  obtain ⟨η, hη⟩ := exists_point_ringKrullDim_stalk_eq_zero (m.fiber (m a)) (m.asFiber a)
  refine ⟨m.fiberι (m a) η, (m.fiberHomeo (m a) η).property, ?_⟩
  rw [ringKrullDim_fiberStalkAt_fiberι]
  exact hη

/-- Given compatible points of the base and the original scheme in a
pullback square, there is a point above both for which the fixed-fibre stalk
dimensions and residue-field transcendence degrees are preserved. -/
theorem exists_point_fiberStalkDim_eq_and_residueFieldTrdegAt_eq_of_isPullback
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') (x : X) (hxs : f x = g s') :
    ∃ x' : X',
      g' x' = x ∧
        f' x' = s' ∧
        ringKrullDim (fiberStalkAt f' x') = ringKrullDim (fiberStalkAt f x) ∧
        f'.residueFieldTrdegAt x' = f.residueFieldTrdegAt x := by
  obtain ⟨x₀, hg₀, hf₀⟩ := Scheme.exists_preimage_of_isPullback hpb x s' hxs
  let z₀ := (f'.fiberHomeo s').symm ⟨x₀, hf₀⟩
  let m := baseChangeFiberMap f g g' f' hpb s'
  have hcomm_morphism : m ≫ f.fiberι (g s') = f'.fiberι s' ≫ g' := by
    exact pullback.lift_fst _ _ _
  have hcomm (z : f'.fiber s') :
      f.fiberι (g s') (m z) = g' (f'.fiberι s' z) := by
    exact congr($(hcomm_morphism) z)
  obtain ⟨z, hz, hzero⟩ := exists_point_fiberStalkAt_eq_zero m z₀
  have hgx : g' (f'.fiberι s' z) = x := by
    rw [← hcomm z, hz, hcomm z₀]
    simpa only [z₀, Scheme.Hom.fiberι_fiberHomeo_symm] using hg₀
  have hzero' : ringKrullDim
      (baseChangeFiberStalkAt f g g' f' hpb (f'.fiberι s' z)) = 0 := by
    generalize ha : f'.fiberι s' z = a
    have hb : f' a = s' := by
      rw [← ha]
      exact (f'.fiberHomeo s' z).property
    cases hb
    have hza : f'.asFiber a = z := by
      apply (f'.fiberι (f' a)).isEmbedding.injective
      simpa using ha.symm
    change ringKrullDim (fiberStalkAt (baseChangeFiberMap f g g' f' hpb (f' a))
      (f'.asFiber a)) = 0
    rw [hza]
    exact hzero
  refine ⟨f'.fiberι s' z, hgx, (f'.fiberHomeo s' z).property, ?_, ?_⟩
  · show ringKrullDim (fiberStalkAt f' (f'.fiberι s' z)) = ringKrullDim (fiberStalkAt f x)
    have hdim := ringKrullDim_baseChangeFiberStalkAt_add_eq_of_isPullback
      f g g' f' hpb (f'.fiberι s' z)
    rw [hzero', zero_add, hgx] at hdim
    exact hdim.symm
  · show f'.residueFieldTrdegAt (f'.fiberι s' z) = f.residueFieldTrdegAt x
    have htr := baseChangeFiberStalkDim_add_trdeg_eq f g g' f' hpb (f'.fiberι s' z)
    rw [hzero', zero_add, hgx] at htr
    exact_mod_cast htr

/-- Under a surjective base change of a locally finite type morphism, every
point lifts to a point with the same residue-field transcendence degree. -/
theorem exists_point_residueFieldTrdegAt_eq_of_isPullback_of_surjective
    {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) [Surjective g] (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (r : ℕ) (x : X)
    (hx : f.residueFieldTrdegAt x = r) :
    ∃ x' : X', g' x' = x ∧ f'.residueFieldTrdegAt x' = r := by
  obtain ⟨s', hs'⟩ := Surjective.surj (f := g) (f x)
  obtain ⟨x', hg', _, _, htr⟩ :=
    exists_point_fiberStalkDim_eq_and_residueFieldTrdegAt_eq_of_isPullback
      f g g' f' hpb s' x hs'.symm
  exact ⟨x', hg', htr.trans hx⟩

/-- Two lifts of a point under a surjective base change of a locally finite
type morphism, both preserving its residue-field transcendence degree, admit
a common lift of the same degree over the double base change, whose projections
are compatible over the original scheme. -/
theorem exists_point_residueFieldTrdegAt_eq_of_doublePullback
    {S X S' X' S'' X'' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) [Surjective g] (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hX' : IsPullback g' f' f g) (pr₁ pr₂ : S'' ⟶ S')
    (hS'' : IsPullback pr₁ pr₂ g g) (p₁ p₂ : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (h₁ : IsPullback p₁ f'' f' pr₁) (h₂ : IsPullback p₂ f'' f' pr₂)
    (hprojection : p₁ ≫ g' = p₂ ≫ g')
    (r : ℕ) (x : X) (hx : f.residueFieldTrdegAt x = r)
    (x₁ x₂ : X') (hx₁ : g' x₁ = x) (hx₂ : g' x₂ = x)
    (htr₁ : f'.residueFieldTrdegAt x₁ = r)
    (htr₂ : f'.residueFieldTrdegAt x₂ = r) :
    ∃ x'' : X'',
      p₁ x'' = x₁ ∧ p₂ x'' = x₂ ∧ f''.residueFieldTrdegAt x'' = r := sorry

end AlgebraicGeometry.Scheme.Hom.FiberDimension
