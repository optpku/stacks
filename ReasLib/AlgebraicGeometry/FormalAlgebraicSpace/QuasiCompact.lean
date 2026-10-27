/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

/-!
# Quasi-compact formal algebraic spaces and morphisms

Object quasi-compactness is characterized by a finite affine étale atlas.
Morphism quasi-compactness is defined using the induced map of explicit reductions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

/-- A morphism of formal algebraic spaces is quasi-compact when its induced morphism
between the given reductions is quasi-compact. -/
def QuasiCompact {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) : Prop :=
  AlgebraicSpace.QuasiCompact (RX.map RY f)

/-- Quasi-compactness is equivalent to quasi-compactness of the induced reduction morphism. -/
theorem quasiCompact_iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    QuasiCompact RX RY f ↔ AlgebraicSpace.QuasiCompact (RX.map RY f) :=
  Iff.rfl

private theorem map_id_eq {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (RX : ReductionData X) :
    RX.map RX (𝟙 X) = 𝟙 RX.space := by
  symm
  apply RX.map_unique RX (𝟙 X)
  change (𝟙 RX.space.functorOfPoints) ≫ RX.ι = RX.ι ≫ 𝟙 X
  simp

private theorem quasiCompact_of_isIso_space {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    AlgebraicSpace.QuasiCompact f := by
  constructor
  intro Z P g pZ pX hZ sq
  haveI : IsIso pZ := sq.isIso_fst_of_isIso
  let eSpace : P ≅ Z := asIso pZ
  let e : P.functorOfPoints ≅ Z.functorOfPoints :=
    { hom := eSpace.hom
      inv := eSpace.inv
      hom_inv_id := eSpace.hom_inv_id
      inv_hom_id := eSpace.inv_hom_id }
  obtain ⟨U, p, hp, hs, hU⟩ :=
    AlgebraicSpace.IsQuasiCompact.exists_compact_etaleCover (X := Z)
  refine ⟨⟨U, p ≫ e.inv, ?_, ?_, hU⟩⟩
  · show (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (p ≫ e.inv)
    exact MorphismProperty.RespectsIso.postcomp _ e.inv p hp
  · show Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (p ≫ e.inv)
    letI := hs
    exact Presheaf.isLocallySurjective_comp _ p e.inv

/-- The identity morphism is quasi-compact on a reduction. -/
theorem quasiCompact_id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (RX : ReductionData X) :
    QuasiCompact RX RX (𝟙 X) := by
  change AlgebraicSpace.QuasiCompact (RX.map RX (𝟙 X))
  rw [map_id_eq]
  exact quasiCompact_of_isIso_space _

/-- An isomorphism of formal algebraic spaces is quasi-compact on their reductions. -/
theorem quasiCompact_of_isIso {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [IsIso f] :
    QuasiCompact RX RY f := by
  haveI : IsIso (RX.map RY f) := by
    refine ⟨⟨RY.map RX (inv f), ?_, ?_⟩⟩
    · show RX.map RY f ≫ RY.map RX (inv f) = 𝟙 RX.space
      rw [← map_comp, IsIso.hom_inv_id, map_id_eq]
    · show RY.map RX (inv f) ≫ RX.map RY f = 𝟙 RY.space
      rw [← map_comp, IsIso.inv_hom_id, map_id_eq]
  exact quasiCompact_of_isIso_space _

/-- For a morphism of formal algebraic spaces representable by algebraic spaces,
quasi-compactness of the induced reduction morphism is equivalent to
quasi-compactness of every scheme Yoneda pullback. -/
theorem quasiCompact_iff_relativeAlgebraicSpaces {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y)
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    QuasiCompact RX RY f ↔
      AlgebraicSpace.relativeAlgebraicSpaces (S := S) (@AlgebraicSpace.QuasiCompact S) f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A quasi-compact formal algebraic space is a formal algebraic space admitting
a finite affine étale covering family. -/
class IsQuasiCompact {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop
    extends IsFormalAlgebraicSpace X where
  /-- There is a finite affine étale covering family of `X`. -/
  exists_finite_etaleAffineCover :
    ∃ (ι : Type u) (_ : Finite ι) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u))
      (π : ∀ i, X_ i ⟶ X), IsEtaleAffineCover π

namespace IsQuasiCompact

/-- A quasi-compact formal algebraic space is formal and admits a finite affine
étale covering family. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsQuasiCompact X] :
    IsFormalAlgebraicSpace X ∧
      ∃ (ι : Type u) (_ : Finite ι) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u))
        (π : ∀ i, X_ i ⟶ X), IsEtaleAffineCover π :=
  ⟨inferInstance, exists_finite_etaleAffineCover (X := X)⟩

/-- Formalness and a finite affine étale covering family imply quasi-compactness. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    (hFormal : IsFormalAlgebraicSpace X)
    (hCover : ∃ (ι : Type u) (_ : Finite ι) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u))
      (π : ∀ i, X_ i ⟶ X), IsEtaleAffineCover π) : IsQuasiCompact X where
  toIsFormalAlgebraicSpace := hFormal
  exists_finite_etaleAffineCover := hCover

/-- Quasi-compactness is equivalent to formalness and existence of a finite
affine étale covering family. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsQuasiCompact X ↔ IsFormalAlgebraicSpace X ∧
      ∃ (ι : Type u) (_ : Finite ι) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u))
        (π : ∀ i, X_ i ⟶ X), IsEtaleAffineCover π :=
  ⟨fun h ↦ @spec S X h, fun ⟨hFormal, hCover⟩ ↦ of hFormal hCover⟩

end IsQuasiCompact

/-- A formal algebraic space is quasi-compact if and only if any specified
reduction is a quasi-compact algebraic space. -/
theorem isQuasiCompact_iff_reduction {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) :
    IsQuasiCompact X ↔ AlgebraicSpace.IsQuasiCompact R.space := sorry

/-- The functor of points of a quasi-compact algebraic space is a quasi-compact
formal algebraic space. -/
instance instIsQuasiCompact_functorOfPoints {S : Scheme.{u}}
    (X : AlgebraicSpace S) [AlgebraicSpace.IsQuasiCompact X] :
    IsQuasiCompact X.functorOfPoints := sorry

/-- A quasi-compact scheme over `S` is quasi-compact as a formal algebraic space. -/
instance instIsQuasiCompact_yoneda {S : Scheme.{u}} (T : Over S)
    [CompactSpace T.left] : IsQuasiCompact (yoneda.obj T) :=
  inferInstanceAs (IsQuasiCompact (AlgebraicSpace.ofOver T).functorOfPoints)

end AlgebraicGeometry.FormalAlgebraicSpace
