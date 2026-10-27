/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic

/-!
# Affine presentations and countable indexing

Affine formal algebraic spaces admit directed affine thickening presentations
and satisfy the representable coequalizer size condition. Countable indexing
means that such a presentation can be indexed by the natural numbers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

private theorem const_affine_thickening_colimit {S : Scheme.{u}} {Λ : Type*}
    [Preorder Λ] [OrderBot Λ] [IsDirected Λ (· ≤ ·)] (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    FormalAlgebraicSpace.IsDirectedAffineThickeningColimit
      ((Functor.const Λ).obj U) (yoneda.obj U) := by
  let c : Cocone (((Functor.const Λ).obj U) ⋙ yoneda) :=
    { pt := yoneda.obj U
      ι := { app := fun _ ↦ 𝟙 _
             naturality := by
               intros
               change yoneda.map (𝟙 U) ≫ 𝟙 (yoneda.obj U) = 𝟙 _ ≫ 𝟙 _
               rw [yoneda.map_id] } }
  refine ⟨?_, ?_, AlgebraicSpace.ofOver_isSheaf U, ?_⟩
  · intro i
    change AlgebraicGeometry.IsAffine U.left
    infer_instance
  · intro i j f
    change IsThickening (𝟙 U.left)
    exact { toIsClosedImmersion := inferInstance, toSurjective := inferInstance }
  · refine ⟨c, 𝟙 _, ⟨?_⟩, inferInstance, inferInstance⟩
    refine { desc := fun s ↦ s.ι.app ⊥, fac := ?_, uniq := ?_ }
    · intro s j
      have h := s.w (homOfLE (bot_le : (⊥ : Λ) ≤ j))
      change yoneda.map (𝟙 U) ≫ s.ι.app j = s.ι.app ⊥ at h
      change 𝟙 (yoneda.obj U) ≫ s.ι.app ⊥ = s.ι.app j
      dsimp [Functor.const] at h ⊢
      simpa only [yoneda.map_id, Category.id_comp] using h.symm
    · intro s m hm
      have h := hm ⊥
      change 𝟙 (yoneda.obj U) ≫ m = s.ι.app ⊥ at h
      simpa only [Category.id_comp] using h

private theorem isAlgebraicSpace_of_yoneda_iso {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (e : F ≅ yoneda.obj U) :
    AlgebraicSpace.IsAlgebraicSpace F := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).mpr (AlgebraicSpace.ofOver_isSheaf U),
    ?_, ⟨U, e.inv, ?_, inferInstance⟩⟩
  · apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro V f
    have hf : yoneda.relativelyRepresentable (f ≫ e.hom) := by
      rw [← yoneda.map_preimage (f ≫ e.hom)]
      exact Functor.relativelyRepresentable.map _ _
    simpa using MorphismProperty.comp_mem _ _ _ hf
      (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
  · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro a b g fst snd h
    have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
    have : IsIso snd := isIso_of_reflects_iso snd yoneda
    have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
    change AlgebraicGeometry.Etale snd.left
    infer_instance

/-- A functor of points on schemes over `S` is an affine formal algebraic space
when it is a directed affine thickening colimit and is a coequalizer of two
maps of representable sheaves. -/
class IsAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- There is a directed affine thickening presentation of `X`. -/
  exists_colimit :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X
  /-- There exist schemes `U`, `R` over `S` with fppf-locally surjective maps
  `yoneda.obj U ⟶ X` and `yoneda.obj R ⟶ U ×_X U`. -/
  exists_presentation :
    ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ

namespace IsAffine

/-- A directed affine thickening colimit with a representable coequalizer
presentation is an affine formal algebraic space. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} {Λ : Type u}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    (hcolim : FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X)
    {U R : Over S} (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU)
    (hπU : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU)
    (hσ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ) :
    IsAffine X :=
  ⟨⟨Λ, inferInstance, inferInstance, D, hcolim⟩, ⟨U, R, πU, σ, hπU, hσ⟩⟩

/-- An affine formal algebraic space unpacks as a directed affine thickening
colimit together with a representable coequalizer presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X] :
    (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) ∧
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  ⟨IsAffine.exists_colimit, IsAffine.exists_presentation⟩

/-- Affine formal algebraic spaces are exactly directed affine thickening
colimits satisfying the coequalizer size condition. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsAffine X ↔
      (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ Over S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) ∧
        ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X)
          (σ : yoneda.obj R ⟶ pullback πU πU),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ :=
  ⟨fun h ↦ ⟨h.exists_colimit, h.exists_presentation⟩,
    fun ⟨hcolim, hpresentation⟩ ↦ ⟨hcolim, hpresentation⟩⟩

/-- The representable functor of an affine scheme over `S` is an affine formal
algebraic space, via the constant directed system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsAffine (yoneda.obj U) :=
  ⟨⟨PUnit.{u + 1}, inferInstance, inferInstance, (Functor.const _).obj U,
      const_affine_thickening_colimit U⟩,
    ⟨U, U, 𝟙 _, inv (pullback.fst (𝟙 (yoneda.obj U)) (𝟙 _)),
      inferInstance, inferInstance⟩⟩

/-- An affine formal algebraic space is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X] :
    IsFormalAlgebraicSpace X := by
  obtain ⟨Λ, hΛ, hdir, D, hD⟩ := IsAffine.exists_colimit (X := X)
  have hrep : AlgebraicSpace.representableByAlgebraicSpaces (𝟙 X) := by
    intro U ξ
    exact isAlgebraicSpace_of_yoneda_iso (asIso (pullback.fst ξ (𝟙 X)))
  refine ⟨hD.isSheaf, ?_, IsAffine.exists_presentation⟩
  refine ⟨PUnit.{u + 1}, fun _ ↦ X, fun _ ↦ 𝟙 X,
    fun _ ↦ ⟨Λ, hΛ, hdir, D, hD⟩, fun _ ↦ hrep, ?_, ?_⟩
  · intro i ha U ξ
    constructor
    intro V φ hφ
    exact MorphismProperty.RespectsIso.postcomp _ (pullback.fst ξ (𝟙 X)) φ hφ
  · apply Presheaf.isLocallySurjective_of_surjective
    intro T x
    exact ⟨⟨PUnit.unit, x⟩, rfl⟩

end IsAffine


/-- An affine formal algebraic space is countably indexed when it admits an
`ℕ`-indexed directed affine thickening presentation. -/
class IsCountablyIndexedAffine {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop
    extends IsAffine X where
  /-- There is an `ℕ`-indexed directed affine thickening presentation of
  `X`. -/
  exists_nat_colimit :
    ∃ D : ℕ ⥤ Over S, FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X

namespace IsCountablyIndexedAffine

/-- An affine formal algebraic space admitting an `ℕ`-indexed directed affine
thickening presentation is countably indexed. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsAffine X]
    (D : ℕ ⥤ Over S) (h : FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X) :
    IsCountablyIndexedAffine X :=
  { toIsAffine := inferInstance
    exists_nat_colimit := ⟨D, h⟩ }

/-- A countably indexed affine formal algebraic space unpacks as an affine
formal algebraic space together with an `ℕ`-indexed directed affine thickening
presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsCountablyIndexedAffine X] :
    IsAffine X ∧ ∃ D : ℕ ⥤ Over S, FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X :=
  ⟨inferInstance, IsCountablyIndexedAffine.exists_nat_colimit⟩

/-- An affine formal algebraic space is countably indexed if and only if it
admits an `ℕ`-indexed directed affine thickening presentation. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsCountablyIndexedAffine X ↔
      IsAffine X ∧ ∃ D : ℕ ⥤ Over S, FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X :=
  ⟨fun h ↦ ⟨h.toIsAffine, h.exists_nat_colimit⟩,
    fun ⟨haffine, hcolim⟩ ↦ { toIsAffine := haffine, exists_nat_colimit := hcolim }⟩

/-- The representable functor of an affine scheme over `S` is countably
indexed, via the constant sequential system. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] :
    IsCountablyIndexedAffine (yoneda.obj U) :=
  { toIsAffine := inferInstance
    exists_nat_colimit := ⟨(Functor.const ℕ).obj U, const_affine_thickening_colimit U⟩ }

end IsCountablyIndexedAffine


end AlgebraicGeometry.AffineFormalAlgebraicSpace
