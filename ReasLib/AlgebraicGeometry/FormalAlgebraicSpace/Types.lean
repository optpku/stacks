/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Local countable indexing, adic and Noetherian types of formal algebraic spaces

These properties use representable etale atlases on the same functor-of-points carrier
as the canonical formal-space definition, with the canonical compatible affine presentations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The singleton identity atlas transfers any property of its only chart. -/
private theorem exists_identity_type_atlas {S : Scheme.{u}}
    (P : ((Over S)ᵒᵖ ⥤ Type u) → Prop) (X : (Over S)ᵒᵖ ⥤ Type u) (hX : P X) :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, P (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
              (AlgebraicGeometry.FormalAlgebraicSpace.sigmaDesc π) := by
  refine ⟨PUnit.{u + 1}, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ hX, ?_, ?_, ?_⟩
  · intro i U ξ
    let e := asIso (pullback.fst ξ (𝟙 X))
    refine ⟨(Presheaf.isSheaf_of_iso_iff e).mpr (ofOver_isSheaf U), ?_, ?_⟩
    · apply Functor.relativelyRepresentable.diag_of_map_from_obj
      intro V f
      rw [← yoneda.relativelyRepresentable.cancel_right_of_respectsIso f e.hom]
      rw [← yoneda.map_preimage (f ≫ e.hom)]
      exact Functor.relativelyRepresentable.map _ _
    · refine ⟨U, e.inv, ?_, inferInstance⟩
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro a b g fst snd h
      have : IsIso (yoneda.map snd) := h.isIso_snd_of_isIso
      have : IsIso snd := isIso_of_reflects_iso snd yoneda
      have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
      change AlgebraicGeometry.Etale snd.left
      infer_instance
  · intro i ha U ξ
    have hfst : IsIso (C := (Over S)ᵒᵖ ⥤ Type u) (pullback.fst ξ (𝟙 X)) :=
      (IsPullback.of_hasPullback ξ (𝟙 X)).isIso_fst_of_isIso
    refine ⟨?_⟩
    intro V φ hφ
    change (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
      (Over.forget S)).presheaf (φ ≫ pullback.fst ξ (𝟙 X))
    let Q : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale) (Over.forget S)).presheaf
    exact (@MorphismProperty.cancel_right_of_respectsIso
      ((Over S)ᵒᵖ ⥤ Type u) _ Q _ (yoneda.obj V) (pullback ξ (𝟙 X)) (yoneda.obj U)
      φ (pullback.fst ξ (𝟙 X)) hfst).mpr hφ
  · apply Presheaf.isLocallySurjective_of_surjective
    intro T x
    exact ⟨⟨PUnit.unit, x⟩, rfl⟩


/-- A formal algebraic space over `S` is locally countably indexed when it
admits an étale atlas by countably indexed affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyCountablyIndexed {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by countably indexed affine formal algebraic
  spaces, representable by algebraic spaces and jointly fppf-locally
  surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyCountablyIndexed

/-- A locally countably indexed formal algebraic space admits an étale atlas by
countably indexed affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyCountablyIndexed X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ‹IsLocallyCountablyIndexed X›.exists_atlas

/-- Locally countably indexed formal algebraic spaces are exactly formal
algebraic spaces with an étale atlas by countably indexed affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyCountablyIndexed X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (cover i)) ∧
          (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : AlgebraicSpace.representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ⟨fun h ↦ h.exists_atlas, fun h ↦ ⟨h⟩⟩

end IsLocallyCountablyIndexed


/-- A formal algebraic space over `S` is locally adic* when it admits an étale
atlas by adic* affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by adic* affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyAdicStar

/-- A locally adic* formal algebraic space admits an étale atlas by adic*
affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyAdicStar X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsAdicStarAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ‹IsLocallyAdicStar X›.exists_atlas

/-- Locally adic* formal algebraic spaces are exactly formal algebraic spaces
with an étale atlas by adic* affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyAdicStar X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsAdicStarAffine (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ⟨fun h ↦ h.exists_atlas, fun h ↦ ⟨h⟩⟩

end IsLocallyAdicStar

namespace IsAdicStarAffine

/-- An adic* affine formal algebraic space that is a formal algebraic space is
locally adic*. -/
instance instIsLocallyAdicStar {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsAdicStarAffine X] : IsLocallyAdicStar X :=
  ⟨exists_identity_type_atlas IsAdicStarAffine X inferInstance⟩

end IsAdicStarAffine

/-- A formal algebraic space over `S` is locally Noetherian when it admits an
étale atlas by Noetherian affine formal algebraic spaces. -/
@[mk_iff]
class IsLocallyNoetherian {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [formalSpace : IsFormalAlgebraicSpace X] : Prop where
  /-- There is an étale atlas by Noetherian affine formal algebraic spaces,
  representable by algebraic spaces and jointly fppf-locally surjective. -/
  exists_noetherian_atlas :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsLocallyNoetherian

/-- The representable functor of a Noetherian affine scheme over `S` is a
locally Noetherian formal algebraic space. -/
instance instYoneda {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left] :
    IsLocallyNoetherian (yoneda.obj U) :=
  ⟨exists_identity_type_atlas IsNoetherianAffine (yoneda.obj U) inferInstance⟩

/-- A locally Noetherian formal algebraic space admits an étale atlas by
Noetherian affine formal algebraic spaces. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
      (∀ i, IsNoetherianAffine (cover i)) ∧
        (∀ i, representableByAlgebraicSpaces (π i)) ∧
          (∀ i (ha : representableByAlgebraicSpaces (π i))
            {U : Over S} (ξ : yoneda.obj U ⟶ X),
            AlgebraicSpace.Etale
              (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ‹IsLocallyNoetherian X›.exists_noetherian_atlas

/-- Locally Noetherian formal algebraic spaces are exactly formal algebraic
spaces with an étale atlas by Noetherian affine charts. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    IsLocallyNoetherian X ↔
      ∃ (ι : Type u) (cover : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (i : ι) → cover i ⟶ X),
        (∀ i, IsNoetherianAffine (cover i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i (ha : representableByAlgebraicSpaces (π i))
              {U : Over S} (ξ : yoneda.obj U ⟶ X),
              AlgebraicSpace.Etale
                (representableByAlgebraicSpaces.pullbackHom ha ξ)) ∧
              Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ⟨fun h ↦ h.exists_noetherian_atlas, fun h ↦ ⟨h⟩⟩

end IsLocallyNoetherian

namespace IsNoetherianAffine

/-- A Noetherian affine formal algebraic space that is a formal algebraic space
is locally Noetherian. -/
instance instIsLocallyNoetherian {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsNoetherianAffine X] : IsLocallyNoetherian X :=
  ⟨exists_identity_type_atlas IsNoetherianAffine X inferInstance⟩

end IsNoetherianAffine

end AlgebraicGeometry.FormalAlgebraicSpace

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine

/-- A countably indexed affine formal algebraic space that is a formal algebraic
space is locally countably indexed. -/
instance instIsLocallyCountablyIndexed {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u)
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X] [IsCountablyIndexedAffine X] :
    FormalAlgebraicSpace.IsLocallyCountablyIndexed X :=
  ⟨FormalAlgebraicSpace.exists_identity_type_atlas IsCountablyIndexedAffine X inferInstance⟩

end AlgebraicGeometry.AffineFormalAlgebraicSpace.IsCountablyIndexedAffine
