/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.FiniteEvaluation

/-!
# Operations on finite locally free scheme morphisms

This file contains characterization, composition, base-change, and
constant-rank decomposition APIs for finite locally free scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

set_option backward.isDefEq.respectTransparency false in
private theorem exists_affine_finiteFree_of_isFiniteLocallyFree
    (h : IsFiniteLocallyFree f) (x : X) :
    ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ (U : X.Opens))
      (e : U ≤ f ⁻¹ᵁ V), (f.appLE V U e).hom.FiniteFree := by
  classical
  letI : IsFiniteLocallyFree f := h
  letI : ∀ U : S.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology S).over U)
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  letI : ∀ U : S.Opens,
      ((Opens.grothendieckTopology S).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  obtain ⟨q, hfree, hfinite⟩ := h.pushforward_isFiniteLocallyFree.exists_data
  letI := hfree
  have hcover : (⨆ i, q.X i) = ⊤ := by
    simpa only [Opens.coversTop_iff, IsOpenCover] using q.coversTop
  have hx : f x ∈ ⨆ i, q.X i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset hi
  letI := hfinite.isFiniteType i
  letI : Algebra (Γ(S, V)) (Γ(X, f ⁻¹ᵁ V)) := (f.app V).hom.toAlgebra
  let b := (q.generators i).basis (Opposite.op (Over.mk (homOfLE hVi)))
  have hmap : (f.app V).hom.FiniteFree :=
    ⟨Module.Finite.of_basis b, Module.Free.of_basis b⟩
  exact ⟨⟨V, hV⟩, ⟨f ⁻¹ᵁ V, hV.preimage f⟩, hxV, le_rfl,
    by simpa [Scheme.Hom.appLE] using hmap⟩

/-- A morphism is finite locally free exactly when it is finite, flat, and locally of finite
presentation. -/
theorem finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := sorry

/-- Construct a finite locally free morphism from finiteness, flatness, and local finite
presentation. -/
theorem isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
    (hfinite : IsFinite f) (hflat : Flat f) (hlfp : LocallyOfFinitePresentation f) :
    IsFiniteLocallyFree f :=
  finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation.mpr
    ⟨hfinite, hflat, hlfp⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite locally free morphism is finite. Local finite bases evaluate to finite bases
of section algebras on an affine cover; finiteness then descends along that cover. -/
theorem IsFiniteLocallyFree.isFinite
    (h : IsFiniteLocallyFree f) :
    IsFinite f := by
  classical
  letI : IsFiniteLocallyFree f := h
  letI : ∀ U : S.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology S).over U)
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  letI : ∀ U : S.Opens,
      ((Opens.grothendieckTopology S).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  obtain ⟨q, hfree, hfinite⟩ := h.pushforward_isFiniteLocallyFree.exists_data
  letI := hfree
  let T := {V : S.affineOpens // ∃ i : q.I, (V : S.Opens) ≤ q.X i}
  have hqcover : (⨆ i, q.X i) = ⊤ := by
    simpa only [Opens.coversTop_iff, IsOpenCover] using q.coversTop
  have hcover : (⨆ V : T, (V.1 : S.Opens)) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ ⨆ i, q.X i := by rw [hqcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVi⟩, hxV⟩
  apply HasAffineProperty.of_iSup_eq_top (P := @IsFinite) (fun V : T ↦ V.1) hcover
  intro V
  obtain ⟨i, hVi⟩ := V.2
  letI := hfinite.isFiniteType i
  letI : Algebra (Γ(S, V.1)) (Γ(X, f ⁻¹ᵁ V.1)) := (f.app V.1).hom.toAlgebra
  let b := (q.generators i).basis (Opposite.op (Over.mk (homOfLE hVi)))
  have hmap : (f.app V.1).hom.Finite := Module.Finite.of_basis b
  refine ⟨V.1.2.preimage f, ?_⟩
  have htop : (f ∣_ V.1).appTop =
      V.1.1.topIso.hom ≫ f.app V.1 ≫ (f ⁻¹ᵁ V.1).topIso.inv := by
    simpa [Scheme.Hom.resLE, Scheme.Hom.app_eq_appLE] using
      (Scheme.Hom.resLE_app_top f (U := V.1) (V := f ⁻¹ᵁ V.1) le_rfl)
  rw [htop, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ V.1).topIso.inv).2).comp
      (hmap.comp (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso V.1.1.topIso.hom).2))

/-- A finite locally free morphism is flat. -/
theorem IsFiniteLocallyFree.flat
    (h : IsFiniteLocallyFree f) :
    Flat f := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left).mpr
  intro x
  obtain ⟨V, U, hx, e, hfree⟩ := exists_affine_finiteFree_of_isFiniteLocallyFree h x
  refine ⟨V, U, hx, e, ?_⟩
  letI := (f.appLE V U e).hom.toAlgebra
  letI := hfree.2
  exact (inferInstance : Module.Flat (Γ(S, V)) (Γ(X, U)))

/-- A finite locally free morphism is locally of finite presentation. -/
theorem IsFiniteLocallyFree.locallyOfFinitePresentation
    (h : IsFiniteLocallyFree f) :
    LocallyOfFinitePresentation f := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left).mpr
  intro x
  obtain ⟨V, U, hx, e, hfree⟩ := exists_affine_finiteFree_of_isFiniteLocallyFree h x
  refine ⟨V, U, hx, e, ?_⟩
  letI := (f.appLE V U e).hom.toAlgebra
  letI : Module.Finite (Γ(S, V)) (Γ(X, U)) := hfree.1
  letI := hfree.2
  letI := Module.finitePresentation_of_projective (Γ(S, V)) (Γ(X, U))
  exact (inferInstance : Algebra.FinitePresentation (Γ(S, V)) (Γ(X, U)))

/-- Finite local freeness supplies finiteness to typeclass search. -/
instance instIsFiniteOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    IsFinite f := IsFiniteLocallyFree.isFinite inferInstance

/-- Finite local freeness supplies flatness to typeclass search. -/
instance instFlatOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    Flat f := IsFiniteLocallyFree.flat inferInstance

/-- Finite local freeness supplies local finite presentation to typeclass search. -/
instance instLocallyOfFinitePresentationOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    LocallyOfFinitePresentation f := IsFiniteLocallyFree.locallyOfFinitePresentation inferInstance

/-- A morphism is finite locally free exactly when it is finite and satisfies the
affine-neighborhood finite-free ring-map condition. The finiteness condition is needed:
every open immersion satisfies the source-local condition. -/
theorem finiteLocallyFree_iff_locallyOfType_ringHomFiniteFree :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ LocallyOfType RingHom.FiniteFree f := by
  constructor
  · intro h
    refine ⟨h.isFinite, ⟨fun x ↦ ?_⟩⟩
    obtain ⟨V, U, hx, e, hfree⟩ := exists_affine_finiteFree_of_isFiniteLocallyFree h x
    exact ⟨U, hx, V, e, hfree⟩
  · rintro ⟨hfinite, hlocal⟩
    refine isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
      hfinite ?_ ?_
    · apply (HasRingHomProperty.iff_exists_appLE (P := @Flat)
        (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
          RingHom.Flat.holdsForLocalizationAway).left).mpr
      intro x
      obtain ⟨U, hx, V, e, hfree⟩ := hlocal.property x
      refine ⟨V, U, hx, e, ?_⟩
      letI := (f.appLE V U e).hom.toAlgebra
      letI := hfree.2
      exact (inferInstance : Module.Flat (Γ(S, V)) (Γ(X, U)))
    · apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
        (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
          RingHom.finitePresentation_holdsForLocalizationAway).left).mpr
      intro x
      obtain ⟨U, hx, V, e, hfree⟩ := hlocal.property x
      refine ⟨V, U, hx, e, ?_⟩
      letI := (f.appLE V U e).hom.toAlgebra
      letI : Module.Finite (Γ(S, V)) (Γ(X, U)) := hfree.1
      letI := hfree.2
      letI := Module.finitePresentation_of_projective (Γ(S, V)) (Γ(X, U))
      exact (inferInstance : Algebra.FinitePresentation (Γ(S, V)) (Γ(X, U)))

/-- A finite locally free morphism satisfies the affine-local finite-free ring-map condition. -/
theorem IsFiniteLocallyFree.locallyOfType_ringHomFiniteFree
    (h : IsFiniteLocallyFree f) :
    LocallyOfType RingHom.FiniteFree f := by
  constructor
  intro x
  obtain ⟨V, U, hx, e, hfree⟩ := exists_affine_finiteFree_of_isFiniteLocallyFree h x
  exact ⟨U, hx, V, e, hfree⟩

/-- Finite local freeness supplies the affine-local finite-free ring-map condition to typeclass
search. -/
instance instLocallyOfTypeRingHomFiniteFreeOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    LocallyOfType RingHom.FiniteFree f :=
  IsFiniteLocallyFree.locallyOfType_ringHomFiniteFree inferInstance

/-- Over a locally Noetherian base, finite local freeness is equivalent to finiteness and
flatness. -/
theorem finiteLocallyFree_iff_isFinite_and_flat [IsLocallyNoetherian S] :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f := by
  constructor
  · intro h
    exact ⟨h.isFinite, h.flat⟩
  · rintro ⟨hfinite, hflat⟩
    letI := hfinite
    exact isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
      hfinite hflat inferInstance

end

/-- Finite locally free scheme morphisms form a morphism property stable under composition. -/
instance finiteLocallyFree_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsFiniteLocallyFree where
  comp_mem f g hf hg := by
    letI := hf.isFinite
    letI := hg.isFinite
    letI := hf.flat
    letI := hg.flat
    letI := hf.locallyOfFinitePresentation
    letI := hg.locallyOfFinitePresentation
    exact isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
      inferInstance inferInstance inferInstance

namespace IsFiniteLocallyFree

/-- The composite of two finite locally free morphisms is finite locally free. -/
theorem comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFiniteLocallyFree f) (hg : IsFiniteLocallyFree g) :
    IsFiniteLocallyFree (f ≫ g) :=
  MorphismProperty.comp_mem @IsFiniteLocallyFree f g hf hg

/-- A finite locally free morphism remains finite locally free after arbitrary base change. -/
theorem pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hf : IsFiniteLocallyFree f) :
    IsFiniteLocallyFree (pullback.snd f g) := by
  letI := hf.isFinite
  letI := hf.flat
  letI := hf.locallyOfFinitePresentation
  exact isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
    inferInstance inferInstance inferInstance

end IsFiniteLocallyFree

/-- Typeclass form of closure of finite locally free morphisms under composition. -/
instance instIsFiniteLocallyFreeComp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsFiniteLocallyFree f] [IsFiniteLocallyFree g] :
    IsFiniteLocallyFree (f ≫ g) := IsFiniteLocallyFree.comp inferInstance inferInstance

/-- Finite locally free scheme morphisms form a morphism property stable under base change. -/
instance finiteLocallyFree_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsFiniteLocallyFree where
  of_isPullback sq hg :=
    isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
      (MorphismProperty.of_isPullback (P := @IsFinite) sq hg.isFinite)
      (MorphismProperty.of_isPullback (P := @Flat) sq hg.flat)
      (MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq
        hg.locallyOfFinitePresentation)

/-- Typeclass form of closure of finite locally free morphisms under base change. -/
instance instIsFiniteLocallyFreePullbackSndOfIsFiniteLocallyFree
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsFiniteLocallyFree f] :
    IsFiniteLocallyFree (pullback.snd f g) :=
  IsFiniteLocallyFree.pullback_snd f g inferInstance

section

variable {X S : Scheme.{u}}

/-- A finite locally free morphism has a clopen decomposition of the base on which its rank is
constant. -/
theorem exists_clopen_degree_decomposition_of_isFiniteLocallyFree
    (f : X ⟶ S) [IsFiniteLocallyFree f] :
    ∃ Sdegree : ℕ → S.Opens,
      iSup Sdegree = ⊤ ∧
        Pairwise (fun d e ↦ Disjoint (Sdegree d : Set S) (Sdegree e : Set S)) ∧
        (∀ d, IsClopen (Sdegree d : Set S)) ∧
        ∀ d, IsFiniteLocallyFreeOfRank (f ∣_ (Sdegree d)) d := sorry

end

end AlgebraicGeometry
