/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import ReasLib.CategoryTheory.Sites.QuasiCompact
public import ReasLib.CategoryTheory.Sites.Family.CoverLifting
public import ReasLib.CategoryTheory.Sites.Point.Construction

/-!
# Finite refinements of site coverings

The chosen-cover and sieve-saturated versions are separate owners: a chosen cover is additional
presentation data, whereas a Grothendieck topology is already saturated under generated sieves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe w u v q w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Precoverage

/-- A chosen-cover site object has the finite-refinement property when every chosen cover admits
a finite chosen cover which factors through it. -/
class HasFiniteRefinement (K : Precoverage C) (U : C) : Prop where
  finite_refinement (R : Presieve U) (hR : R ∈ K U) :
    ∃ (S : Presieve U), S ∈ K U ∧ S.uncurry.Finite ∧ S.FactorsThru R

/-- A chosen-cover site object has the finite-subcover property when every chosen cover contains a
finite selected subfamily which is still a chosen cover. -/
class HasFiniteSubcover (K : Precoverage C) (U : C) : Prop where
  finite_subcover (R : Presieve U) (hR : R ∈ K U) :
    ∃ (T : Set R.uncurry), T.Finite ∧ R.subfamily T ∈ K U

/-- The finite-refinement property in the fixed-target-family presentation. -/
theorem HasFiniteRefinement.finite_refinement_of_family
    {K : Precoverage C} {U : C} (hU : K.HasFiniteRefinement U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toPresieve ∈ K U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toPresieve ∈ K U), Nonempty (𝒱 ⟶ 𝒰) := by
  classical
  obtain ⟨S, hS, hfin, hfactor⟩ := hU.finite_refinement 𝒰.toPresieve h𝒰
  let 𝒲 : SemiRepresentableFamily.Over.{max u v} U :=
    ⟨S.uncurry, fun i ↦ CategoryTheory.Over.mk i.1.2⟩
  letI : Finite 𝒲.index := hfin.to_subtype
  let 𝒱 : SemiRepresentableFamily.Over.{w} U := ofArrows
    (fun i : ULift.{w} (finReindex 𝒲).index ↦ ((finReindex 𝒲).obj i.down).left)
    (fun i ↦ ((finReindex 𝒲).obj i.down).hom)
  letI : Finite 𝒱.index := by
    change Finite (ULift.{w} (Fin (Nat.card 𝒲.index)))
    infer_instance
  have h𝒱 : 𝒱.toPresieve = S := by
    have hsurj : Function.Surjective
        (fun i : 𝒱.index ↦ (Finite.equivFin 𝒲.index).symm i.down) := by
      intro i
      exact ⟨ULift.up (Finite.equivFin 𝒲.index i),
        (Finite.equivFin 𝒲.index).symm_apply_apply i⟩
    refine (Presieve.ofArrows_comp_eq_of_surjective
      (fun i : 𝒲.index ↦ (𝒲.obj i).hom) hsurj).trans ?_
    apply le_antisymm
    · rintro _ _ ⟨i⟩
      exact i.2
    · intro Y f hf
      exact Presieve.ofArrows.mk (⟨⟨Y, f⟩, hf⟩ : S.uncurry)
  have hcomponent (i : 𝒱.index) :
      ∃ j : 𝒰.index, ∃ f : (𝒱.obj i).left ⟶ (𝒰.obj j).left,
        f ≫ (𝒰.obj j).hom = (𝒱.obj i).hom := by
    have hi : S (𝒱.obj i).hom := h𝒱 ▸ Presieve.ofArrows.mk i
    obtain ⟨W, f, g, hg, hfg⟩ := hfactor hi
    cases hg with
    | mk j => exact ⟨j, f, hfg⟩
  choose α f hf using hcomponent
  exact ⟨𝒱, inferInstance, h𝒱.symm ▸ hS, ⟨{
    α := α
    f := fun i ↦ CategoryTheory.Over.homMk (f i) (hf i) }⟩⟩

/-- A finite chosen subcover induces a finite chosen refinement. -/
theorem HasFiniteSubcover.toFiniteRefinement
    {K : Precoverage C} {U : C} (hU : K.HasFiniteSubcover U) :
    K.HasFiniteRefinement U := by
  refine ⟨fun R hR ↦ ?_⟩
  obtain ⟨T, hfin, hT⟩ := hU.finite_subcover R hR
  letI := hfin.to_subtype
  refine ⟨R.subfamily T, hT, ?_, ?_⟩
  · show (R.subfamily T).uncurry.Finite
    rw [Presieve.uncurry_ofArrows]
    exact Set.finite_range _
  · show (R.subfamily T).FactorsThru R
    apply Presieve.factorsThru_of_le
    rintro _ _ ⟨i⟩
    exact i.1.2

/-- A finite chosen refinement implies chosen-cover quasi-compactness. -/
theorem HasFiniteRefinement.quasiCompact
    {K : Precoverage C} {U : C} (hU : K.HasFiniteRefinement U) :
    K.QuasiCompactObject U := by
  classical
  intro R hR
  obtain ⟨S, hS, hfin, hfactor⟩ := hU.finite_refinement R hR
  have hcomponent (i : S.uncurry) :
      ∃ j : R.uncurry, ∃ f : i.1.1 ⟶ j.1.1, f ≫ j.1.2 = i.1.2 := by
    obtain ⟨W, f, g, hg, hfg⟩ := hfactor i.2
    exact ⟨⟨⟨W, g⟩, hg⟩, f, hfg⟩
  choose α f hf using hcomponent
  letI := hfin.to_subtype
  refine ⟨S, hS, Set.range α, Set.finite_range α, ?_⟩
  intro Z g hg
  let i : S.uncurry := ⟨⟨Z, g⟩, hg⟩
  exact ⟨(α i).1.1, f i, (α i).1.2,
    Presieve.ofArrows.mk (⟨α i, Set.mem_range_self i⟩ : Set.range α), hf i⟩

namespace HasFiniteRefinement.Counterexample

/-- There are chosen-cover sites where quasi-compactness does not imply the finite-refinement
property. The category and pullback structures are existential data, so their `letI` binders are
scoped to the chosen counterexample rather than installed as ambient instances. -/
theorem quasiCompact :
    ∃ (D : Type u) (categoryD : Category.{v} D)
      (pullbacksD : Limits.HasPullbacks D),
      -- Local instance justification (noncanonical choice): The chosen category types the witness.
      letI : Category.{v} D := categoryD
      -- Local instance justification (noncanonical choice): The chosen pullbacks type the witness.
      letI : Limits.HasPullbacks D := pullbacksD
      ∃ (K : Pretopology D) (V : D),
        K.toPrecoverage.QuasiCompactObject V ∧
          ¬ K.toPrecoverage.HasFiniteRefinement V := sorry

end HasFiniteRefinement.Counterexample

namespace HasFiniteSubcover.Counterexample

/-- There are chosen-cover sites where the finite-refinement property does not imply the finite
selected-subcover property. The category and pullback structures are existential data, so their
`letI` binders are scoped to the chosen counterexample rather than installed globally. -/
theorem finiteRefinement :
    ∃ (D : Type u) (categoryD : Category.{v} D)
      (pullbacksD : Limits.HasPullbacks D),
      -- Local instance justification (noncanonical choice): The chosen category types the witness.
      letI : Category.{v} D := categoryD
      -- Local instance justification (noncanonical choice): The chosen pullbacks type the witness.
      letI : Limits.HasPullbacks D := pullbacksD
      ∃ (K : Pretopology D) (V : D),
        K.toPrecoverage.HasFiniteRefinement V ∧
          ¬ K.toPrecoverage.HasFiniteSubcover V := sorry

end HasFiniteSubcover.Counterexample

end Precoverage

namespace GrothendieckTopology

/-- A Grothendieck-topology object has the finite-refinement property when each generated covering
sieve is refined by a finite covering family. -/
@[stacks 00YQ "finite refinement property"]
class HasFiniteRefinement (J : GrothendieckTopology C) (U : C) : Prop where
  finite_refinement (R : Presieve U) (hR : Sieve.generate R ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toSieve ∈ J U),
      𝒱.toSieve ≤ Sieve.generate R

/-- A Grothendieck-topology object has the finite-subcover property when every generated covering
sieve contains a finite covering subfamily. -/
class HasFiniteSubcover (J : GrothendieckTopology C) (U : C) : Prop where
  finite_subcover (R : Presieve U) (hR : Sieve.generate R ∈ J U) :
    ∃ (T : Set R.uncurry), T.Finite ∧
      Sieve.ofArrows (fun i : T ↦ i.1.1.1) (fun i ↦ i.1.1.2) ∈ J U

/-- The topology-facing finite-refinement property in the fixed-target-family presentation. -/
theorem HasFiniteRefinement.finite_refinement_of_family
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinement J U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱.toSieve ∈ J U),
      𝒱.toSieve ≤ 𝒰.toSieve := by
  exact hU.finite_refinement 𝒰.toPresieve h𝒰

/-- A finite sieve-saturated subcover induces a finite sieve-saturated refinement. -/
theorem HasFiniteSubcover.toFiniteRefinement
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteSubcover J U) :
    HasFiniteRefinement J U := by
  refine ⟨fun R hR ↦ ?_⟩
  obtain ⟨T, hfin, hT⟩ := hU.finite_subcover R hR
  letI := hfin.to_subtype
  refine ⟨ofArrows (fun i : T ↦ i.1.1.1) (fun i ↦ i.1.1.2),
    (by change Finite T; infer_instance), hT, ?_⟩
  apply (Sieve.generate_le_iff _ _).2
  rintro _ _ ⟨i⟩
  exact Sieve.le_generate R _ _ i.1.2

/-- A finite sieve-saturated refinement implies sieve-saturated quasi-compactness. -/
theorem HasFiniteRefinement.quasiCompact
    {J : GrothendieckTopology C} {U : C} (hU : HasFiniteRefinement J U) :
    J.QuasiCompactObject U := by
  intro S
  obtain ⟨𝒱, hfin, h𝒱, hle⟩ := hU.finite_refinement (S : Sieve U).arrows
    (by simpa only [Sieve.generate_sieve] using S.condition)
  letI := hfin
  have hle' : 𝒱.toSieve ≤ (S : Sieve U) := by
    simpa only [Sieve.generate_sieve] using hle
  let α : 𝒱.index → S.Arrow := fun i ↦
    ⟨(𝒱.obj i).left, (𝒱.obj i).hom,
      hle' _ (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i))⟩
  refine ⟨Set.range α, Set.finite_range α, J.superset_covering ?_ h𝒱⟩
  apply (Sieve.generate_le_iff _ _).2
  rintro _ _ ⟨i⟩
  exact Sieve.ofArrows_mk _ _ (⟨α i, Set.mem_range_self i⟩ : Set.range α)

namespace HasFiniteRefinement

/-- A site with finite limits and a finite refinement for every covering sieve has enough
points.  The site-wide hypothesis is explicit rather than an ambient instance so that local
applications do not need to install a noncanonical typeclass. -/
theorem hasEnoughPoints
    {J : GrothendieckTopology C} [Limits.HasFiniteLimits C]
    (hJ : ∀ X : C, HasFiniteRefinement J X) :
    HasEnoughPoints.{max (u + 1) (v + 1)} J := sorry

end HasFiniteRefinement

namespace Point.Fiber

/-- Finite-cover lifting becomes lifting along arbitrary covering sieves when every covering
sieve has a finite refinement.  This is the bridge from the finite-family construction used in
refinement arguments to the canonical point-construction condition. -/
theorem of_finite_cover_lifts
    {J : GrothendieckTopology C} {p : C ⥤ Type q}
    (hJ : ∀ X : C, HasFiniteRefinement J X)
    (hp : Functor.FiniteCoverLifts.{u, v, q, w'} p J) :
    coversLift J p := by
  intro X R hR x
  obtain ⟨𝒱, hfin, h𝒱, hle⟩ := (hJ X).finite_refinement R.arrows
    (by simpa only [Sieve.generate_sieve] using hR)
  letI := hfin
  let 𝒲 : SemiRepresentableFamily.Over.{w'} X := ofArrows
    (fun i : ULift.{w'} (finReindex 𝒱).index ↦ ((finReindex 𝒱).obj i.down).left)
    (fun i ↦ ((finReindex 𝒱).obj i.down).hom)
  letI : Finite 𝒲.index := by
    change Finite (ULift.{w'} (Fin (Nat.card 𝒱.index)))
    infer_instance
  have h𝒲 : 𝒲.toSieve = 𝒱.toSieve := by
    apply congrArg Sieve.generate
    apply Presieve.ofArrows_comp_eq_of_surjective (fun i ↦ (𝒱.obj i).hom)
    intro i
    exact ⟨ULift.up (Finite.equivFin 𝒱.index i),
      (Finite.equivFin 𝒱.index).symm_apply_apply i⟩
  have hle' : 𝒲.toSieve ≤ R := by
    rw [h𝒲]
    simpa only [Sieve.generate_sieve] using hle
  obtain ⟨i, y, hy⟩ := hp 𝒲 (h𝒲.symm ▸ h𝒱) x
  exact ⟨(𝒲.obj i).left, (𝒲.obj i).hom,
    hle' _ (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i)), y, hy⟩

end Point.Fiber

end GrothendieckTopology

end CategoryTheory
