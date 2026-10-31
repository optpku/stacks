/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.Subsheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Completion

variable {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u}

/-- A section belongs to the nth infinitesimal neighbourhood when its
pullback of the subspace is a closed immersion with kernel power `n + 1` zero. -/
def inStage (inclusion : Z ⟶ X) (n : ℕ) {U : Over S} (element : X.obj (op U)) : Prop :=
  ∃ (V : Over S) (projection : V ⟶ U) (morphism : yoneda.obj V ⟶ Z),
    IsPullback morphism (yoneda.map projection) inclusion (yonedaEquiv.symm element) ∧
      IsClosedImmersion projection.left ∧ projection.left.ker ^ (n + 1) = ⊥

/-- Membership in an infinitesimal neighbourhood is stable under restriction. -/
theorem inStage_map (inclusion : Z ⟶ X) (n : ℕ) {U V : Over S}
    (restriction : V ⟶ U) {element : X.obj (op U)}
    (hSection : inStage inclusion n element) :
    inStage inclusion n (X.map restriction.op element) := sorry

/-- The nth infinitesimal neighbourhood, embedded in the ambient presheaf. -/
def stage (inclusion : Z ⟶ X) (n : ℕ) : Subfunctor X where
  obj _ := {element | inStage inclusion n element}
  map restriction _ hSection := inStage_map inclusion n restriction.unop hSection

/-- Stage membership is equivalent to the represented pullback kernel-power
criterion. -/
theorem mem_stage_iff (inclusion : Z ⟶ X) (n : ℕ) {U : Over S}
    (element : X.obj (op U)) :
    element ∈ (stage inclusion n).obj (op U) ↔ inStage inclusion n element := Iff.rfl

/-- The zeroth infinitesimal neighbourhood of a closed subspace is its image. -/
theorem stage_zero (inclusion : Z ⟶ X) [IsAlgebraicSpace X]
    [IsAlgebraicSpace Z]
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion) :
    stage inclusion 0 = Subfunctor.range inclusion := by
  haveI : Mono inclusion := by
    apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms inclusion
    refine ⟨hClosed.1, ?_⟩
    intro U V g fst snd hPullback
    haveI : IsClosedImmersion snd.left := hClosed.property g fst snd hPullback
    exact Over.mono_of_mono_left snd
  ext U element
  constructor
  · intro hSection
    obtain ⟨V, projection, morphism, hPullback, hProjection, hPower⟩ := hSection
    haveI : IsClosedImmersion projection.left := hProjection
    haveI : IsIso projection.left :=
      IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (by simpa [pow_one] using hPower)
    haveI : IsIso ((Over.forget S).map projection) := inferInstanceAs (IsIso projection.left)
    haveI : IsIso projection := isIso_of_reflects_iso projection (Over.forget S)
    refine ⟨yonedaEquiv (inv (yoneda.map projection) ≫ morphism), ?_⟩
    rw [← yonedaEquiv_comp, Category.assoc, hPullback.w, IsIso.inv_hom_id_assoc,
      Equiv.apply_symm_apply]
  · rintro ⟨element, rfl⟩
    refine ⟨U.unop, 𝟙 _, yonedaEquiv.symm element, ?_, ?_, ?_⟩
    · apply IsPullback.of_vert_isIso_mono
      exact CommSq.mk (yonedaEquiv_symm_naturality_right U.unop inclusion element)
    · infer_instance
    · simpa [pow_one] using (Scheme.Hom.ker_eq_bot_of_isIso (𝟙 U.unop.left))

/-- The infinitesimal neighbourhoods form an increasing sequence. -/
theorem stage_mono (inclusion : Z ⟶ X) : Monotone (stage inclusion) := by
  intro m n hOrder U element hSection
  obtain ⟨V, projection, morphism, hPullback, hClosed, hPower⟩ := hSection
  refine ⟨V, projection, morphism, hPullback, hClosed, le_antisymm ?_ bot_le⟩
  calc
    projection.left.ker ^ (n + 1) ≤ projection.left.ker ^ (m + 1) := by
      intro W
      exact Ideal.pow_le_pow_right (Nat.add_le_add_right hOrder 1)
    _ = ⊥ := hPower

/-- Every infinitesimal neighbourhood of a closed algebraic subspace is an
algebraic space. -/
theorem stage_isAlgebraicSpace (inclusion : Z ⟶ X) [IsAlgebraicSpace X]
    [IsAlgebraicSpace Z]
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion)
    (n : ℕ) : IsAlgebraicSpace (stage inclusion n).toFunctor := sorry

/-- The transitions between infinitesimal neighbourhoods are representable
surjective closed immersions. -/
theorem stage_transition_isThickening (inclusion : Z ⟶ X) [IsAlgebraicSpace X]
    [IsAlgebraicSpace Z]
    (hClosed : Scheme.representableMorphismProperty S (@IsClosedImmersion) inclusion)
    {m n : ℕ} (hOrder : m ≤ n) :
    Scheme.representableMorphismProperty S (@IsClosedImmersion ⊓ @Surjective)
      (Subfunctor.homOfLe (stage_mono inclusion hOrder)) := sorry

/-- Completion along a subspace is the fppf sheafified union of all its
infinitesimal neighbourhoods. -/
noncomputable def subfunctor (inclusion : Z ⟶ X) : Subfunctor X :=
  (⨆ n, stage inclusion n).sheafify (Scheme.fppfTopology.over S)

/-- A section of the completion lies locally in an infinitesimal neighbourhood;
the neighbourhood index may vary over the covering sieve. -/
theorem mem_subfunctor_iff (inclusion : Z ⟶ X) {U : Over S}
    (element : X.obj (op U)) :
    element ∈ (subfunctor inclusion).obj (op U) ↔
      ∃ covering : Sieve U, covering ∈ (Scheme.fppfTopology.over S) U ∧
        ∀ (V : Over S) (restriction : V ⟶ U), covering restriction →
          ∃ n : ℕ, inStage inclusion n (X.map restriction.op element) := by
  change (⨆ n, stage inclusion n).sieveOfSection element ∈
    (Scheme.fppfTopology.over S) U ↔ _
  constructor
  · intro hCover
    refine ⟨(⨆ n, stage inclusion n).sieveOfSection element, hCover, ?_⟩
    intro V restriction hSection
    change X.map restriction.op element ∈ (⨆ n, stage inclusion n).obj (op V) at hSection
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion, mem_stage_iff] using hSection
  · rintro ⟨covering, hCover, hSection⟩
    apply (Scheme.fppfTopology.over S).superset_covering ?_ hCover
    intro V restriction hRestriction
    change X.map restriction.op element ∈ (⨆ n, stage inclusion n).obj (op V)
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion, mem_stage_iff] using
      hSection V restriction hRestriction

/-- Completion inside an fppf sheaf is an fppf sheaf. -/
theorem subfunctor_isSheaf (inclusion : Z ⟶ X)
    (hX : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (subfunctor inclusion).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type] at hX ⊢
  exact Subfunctor.sheafify_isSheaf (⨆ n, stage inclusion n) hX

/-- Every infinitesimal neighbourhood is contained in the completion. -/
theorem stage_le (inclusion : Z ⟶ X) (n : ℕ) :
    stage inclusion n ≤ subfunctor inclusion :=
  (le_iSup (stage inclusion) n).trans
    ((⨆ n, stage inclusion n).le_sheafify (Scheme.fppfTopology.over S))

/-- The canonical morphism from an infinitesimal neighbourhood to the completion. -/
noncomputable def fromStage (inclusion : Z ⟶ X) (n : ℕ) :
    (stage inclusion n).toFunctor ⟶ (subfunctor inclusion).toFunctor :=
  Subfunctor.homOfLe (stage_le inclusion n)

/-- The stage-to-completion morphism commutes with the ambient inclusions. -/
theorem fromStage_comp_ι (inclusion : Z ⟶ X) (n : ℕ) :
    fromStage inclusion n ≫ (subfunctor inclusion).ι = (stage inclusion n).ι :=
  Subfunctor.homOfLe_ι (stage_le inclusion n)

end AlgebraicGeometry.AlgebraicSpace.Completion
